#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
#include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();
static inline header * find_freelist_pointer();
static inline header * split_block();
static inline void insert_into_freelist();
static inline void REMOVE_from_freelist();


static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
    return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
    return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
    return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
    set_state(fp,FENCEPOST);
    set_size(fp, ALLOC_HEADER_SIZE);
    fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
    if (numOsChunks < MAX_OS_CHUNKS) {
        osChunkList[numOsChunks++] = hdr;
    }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
    // Convert to char * before performing operations
    char * mem = (char *) raw_mem;

    // Insert a fencepost at the left edge of the block
    header * leftFencePost = (header *) mem;
    initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

    // Insert a fencepost at the right edge of the block
    header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
    initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
    void * mem = sbrk(size);

    insert_fenceposts(mem, size);
    header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
    set_state(hdr, UNALLOCATED);
    set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
    hdr->left_size = ALLOC_HEADER_SIZE;
    return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's requests
 */
static inline header * allocate_object(size_t raw_size) {
    // TODO implement allocation
    if (raw_size == 0) {
        return NULL;
    }

    //calculate the size
    size_t rounded_size = raw_size;

    if (raw_size % 8 != 0) {
        rounded_size += 8 - raw_size % 8;
    }


    size_t actual_size = rounded_size + ALLOC_HEADER_SIZE;

    if (actual_size <= sizeof (header)) {
        actual_size = sizeof (header);
    }

    header *requested_pointer = find_freelist_pointer(actual_size, raw_size);
    assert(requested_pointer != NULL);

    set_state(requested_pointer, ALLOCATED);
    return (header*) requested_pointer->data;

}

static  inline header *find_freelist_pointer(size_t input , size_t raw_size) {
    size_t index = N_LISTS - 1;
    if ((input - ALLOC_HEADER_SIZE) > (N_LISTS - 1) * 8) {
        index = N_LISTS - 1;
    } else {
        index = (input - ALLOC_HEADER_SIZE)/8 - 1;
    }

    for (int i = index; i < N_LISTS; i++) {
        header * freelist = &freelistSentinels[i];
        assert(freelist != NULL);
        header * head_list = freelist;
        header * current_list = freelist->next;

        while(current_list != freelist) {
            if (get_size(current_list) == input){
                current_list->prev->next = current_list->next;

        while(true) {
            if (get_size(current_list) == input){
                current_list->prev->next = current_list->next;
                current_list->next->prev = current_list->prev;
                assert(current_list != NULL);
                return current_list;
            }

            if (get_size(current_list) > input) {
                return split_block(current_list, input);
            }

            if (current_list -> next == head_list) {
                break;
            }
            current_list = current_list -> next;
        }

    }
    return NULL;



}

static inline void add_chunk() {
    header * newHeader = allocate_chunk(ARENA_SIZE);
    header * left_fencepost = get_left_header(newHeader);
    header * prev_right_fencepost = get_left_header(left_fencepost);


//    case 1: new chunk is adjecent and it is unallocated

    if (prev_right_fencepost == lastFencePost) {
        header * prev_header = get_left_header(prev_right_fencepost);
        if (get_state(prev_header) == UNALLOCATED) {
            bool is_free = last_list_check(prev_header);

            set_size(prev_header, get_size(prev_header) + get_size(newHeader) + 2 * ALLOC_HEADER_SIZE);
            set_state(prev_header, UNALLOCATED);
            get_right_header(newHeader)->left_size = get_size(prev_header);
            size_t index = N_LISTS - 1;
            if (!(is_free == true && get_size(prev_header) < ((N_LISTS + 2) * sizeof (header)))) {
                REMOVE_from_freelist(prev_header);
                insert_into_freelist(prev_header);
            }
            lastFencePost = get_right_header(newHeader);

//            case 2: new chunk is adjecent and it is allocated
        } else {
            set_size(prev_right_fencepost, get_size(newHeader) + 2 * ALLOC_HEADER_SIZE);
            get_right_header(newHeader)->left_size = get_size(prev_right_fencepost);
            set_state(prev_right_fencepost, UNALLOCATED);
            insert_into_freelist(prev_right_fencepost);
            lastFencePost = get_right_header(newHeader);
        }
//        case 3: not adjacent
    } else {
        insert_into_freelist(newHeader);
        lastFencePost = get_right_header(newHeader);
        insert_os_chunk(left_fencepost);
    }

}


static inline header * split_block(header * current_list, size_t input) {
    size_t input_block_size = get_size(current_list);
    if (get_size(current_list) - input >= sizeof (header)) {
        size_t left_block_size = get_size(current_list) - input;
        set_size(current_list, left_block_size);
        header* cut_block = current_list;
        header* new_current = get_header_from_offset(current_list, left_block_size);
        assert(new_current != NULL);
        set_size(new_current, input);

        new_current ->left_size = get_size(cut_block);
        header * right_header = get_right_header(new_current);
        right_header->left_size = get_size(new_current);

        if (get_size(cut_block) < (N_LISTS+2) * sizeof(size_t)) {
            cut_block->prev->next = cut_block->next;
            cut_block->next->prev = cut_block->prev;
            insert_into_freelist(cut_block);
        }
        assert(new_current != NULL);
        return new_current;

    } else {
        current_list->prev->next = current_list->next;
        current_list->next->prev = current_list->prev;
        assert(current_list != NULL);
        return current_list;

    }

}



static inline void insert_into_freelist(header * hdr) {
    size_t index = N_LISTS - 1;
    if ((get_size(hdr)- ALLOC_HEADER_SIZE) > (N_LISTS - 1) * 8) {
        index = N_LISTS - 1;
    } else {
        index = (get_size(hdr) - ALLOC_HEADER_SIZE)/8 - 1;
    }

    header * freelist = &freelistSentinels[index];
    freelist->next->prev = hdr;
    hdr->next = freelist->next;
    hdr->prev = freelist;
    freelist->next = hdr;


}

static inline void REMOVE_from_freelist(header * hdr) {
    assert(hdr != NULL);
    if(hdr->prev == NULL && hdr->next == NULL){
        return;
    }

    hdr->prev->next = hdr->next;
    hdr->next->prev = hdr->prev;
}

static inline bool last_list_check(header* hdr) {

    int listidx = N_LISTS - 1;
    if (get_size(hdr) > (N_LISTS - 1) * 8) {
        listidx  = N_LISTS - 1;
    } else{
        listidx = (get_size(hdr) / 8) - 1;
    }


    if (listidx != N_LISTS - 1) {
        return false;
    }

    return true;
}


/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
    return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
    // TODO implement deallocation
    int index = N_LISTS - 1;
    if (p == NULL) {
        return;
    }
    header *real_header = ptr_to_header(p);
    if (get_state(real_header) != ALLOCATED) {
        printf("Double Free Detected\n");
        printf("Assertion Failed!\n");
        assert(true);
        exit(1);
    }
    header *left_location = get_left_header(real_header);
    header *right_location = get_right_header(real_header);
    if (get_state(left_location) != UNALLOCATED && get_state(right_location) != UNALLOCATED) {
        set_state(real_header, UNALLOCATED);
        insert_into_freelist(real_header);

    } else if (get_state(left_location) == UNALLOCATED && get_state(right_location) != UNALLOCATED) {
        bool is_free = last_list_check(left_location);
        set_state(real_header, UNALLOCATED);
        set_size(left_location, get_size(left_location) + get_size(real_header));
        get_right_header(left_location)->left_size = get_size(left_location);
        if (!(is_free == true && get_size(left_location) < ((N_LISTS + 2) * sizeof (header)))) {
            REMOVE_from_freelist(left_location);
            insert_into_freelist(left_location);
        }

    } else if (get_state(left_location) != UNALLOCATED && get_state(right_location) == UNALLOCATED) {
        set_state(real_header, UNALLOCATED);
        REMOVE_from_freelist(right_location);
        set_size(real_header, get_size(real_header) + get_size(right_location));
        get_right_header(real_header)->left_size = get_size(real_header);
        insert_into_freelist(real_header);

    } else if (get_state(left_location) == UNALLOCATED && get_state(right_location) == UNALLOCATED) {
        bool is_free = last_list_check(left_location);
        set_state(real_header, UNALLOCATED);
        REMOVE_from_freelist(right_location);
        set_size(left_location, get_size(left_location) + get_size(real_header) + get_size(right_location));
        get_right_header(left_location)->left_size = get_size(left_location);

        if (!(is_free == true && get_size(left_location) < ((N_LISTS + 2) * sizeof (header)))) {
            REMOVE_from_freelist(left_location);
            insert_into_freelist(left_location);
        }


    }
}


/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
    for (int i = 0; i < N_LISTS; i++) {
        header * freelist = &freelistSentinels[i];
        for (header * slow = freelist->next, * fast = freelist->next->next;
             fast != freelist;
             slow = slow->next, fast = fast->next->next) {
            if (slow == fast) {
                return slow;
            }
        }
    }
    return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
    for (int i = 0; i < N_LISTS; i++) {
        header * freelist = &freelistSentinels[i];
        for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
            if (cur->next->prev != cur || cur->prev->next != cur) {
                return cur;
            }
        }
    }
    return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
    header * cycle = detect_cycles();
    if (cycle != NULL) {
        fprintf(stderr, "Cycle Detected\n");
        print_sublist(print_object, cycle->next, cycle);
        return false;
    }

    header * invalid = verify_pointers();
    if (invalid != NULL) {
        fprintf(stderr, "Invalid pointers\n");
        print_object(invalid);
        return false;
    }

    return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
    if (get_state(chunk) != FENCEPOST) {
        fprintf(stderr, "Invalid fencepost\n");
        print_object(chunk);
        return chunk;
    }

    for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
        if (get_size(chunk)  != get_right_header(chunk)->left_size) {
            fprintf(stderr, "Invalid sizes\n");
            print_object(chunk);
            return chunk;
        }
    }

    return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
    for (size_t i = 0; i < numOsChunks; i++) {
        header * invalid = verify_chunk(osChunkList[i]);
        if (invalid != NULL) {
            return invalid;
        }
    }

    return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
    // Initialize mutex for thread safety
    pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
    // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

    // Allocate the first chunk from the OS
    header * block = allocate_chunk(ARENA_SIZE);

    header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
    insert_os_chunk(prevFencePost);

    lastFencePost = get_header_from_offset(block, get_size(block));

    // Set the base pointer to the beginning of the first fencepost in the first
    // chunk from the OS
    base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

    // Initialize freelist sentinels
    for (int i = 0; i < N_LISTS; i++) {
        header * freelist = &freelistSentinels[i];
        freelist->next = freelist;
        freelist->prev = freelist;
    }

    // Insert first chunk into the free list
    header * freelist = &freelistSentinels[N_LISTS - 1];
    freelist->next = block;
    freelist->prev = block;
    block->next = freelist;
    block->prev = freelist;
}

/*
 * External interface
 */
void * my_malloc(size_t size) {
    pthread_mutex_lock(&mutex);
