/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following.  Be sure not
 * to have debugging enabled in your final submission
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

 /* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

typedef struct block
{
    word_t header;

    union data{
        char payload[0];
        struct list_ptr
        {
            struct block *next;
            struct block *prev;
        } ptr;
    }data;
} block_t;

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size, block_t* prev_block);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

static void insert_to_free_list(block_t *block);
static block_t* get_prev_free(block_t *block);
static block_t* get_next_free(block_t *block);
static block_t* find_tail();
static void link_blocks(block_t *prev, block_t* next);
static void print_free_list();

bool mm_checkheap(int lineno);

static block_t *free_list = NULL;
static block_t *list_tail = NULL;
static block_t *heap_listp = NULL;

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) {
    dbg_printf("Start init.\n");

    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    if (start == (void *)-1)
    {
        return false;
    }
    start[0] = pack(0, true);
    start[1] = pack(1, true);
    heap_listp = (block_t *) &(start[1]);
    free_list = NULL;

    dbg_printf("Before extend heap.\n");
    if (extend_heap(chunksize, NULL) == NULL) {
      return false;
    }

    dbg_printf("Finish init.\n");

    print_free_list();
    return true;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;
    size_t extendsize;
    block_t *block;
    void *bp = NULL;

    dbg_printf("Malloc size %d.\n", (int)size);

    if (heap_listp == NULL)
    {
        mm_init();
    }

    if (size == 0)
    {
        return bp;
    }

    asize = round_up(size, dsize) + dsize;
    block = find_fit(asize);
    dbg_printf("Fit block: %p\n", (void*)block);

    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize, find_tail());
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
        print_free_list();
    }

    place(block, asize);
    dbg_printf("Place block: %p\n", (void*)block);
    bp = header_to_payload(block);

    dbg_printf("Malloc size %zd on address %p.\n", size, bp);
    dbg_ensures(mm_checkheap);
    print_free_list();
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(ptr);
    size_t size = get_size(block);
    dbg_printf("Free block at addr %p with size %d.\n", (void*)block, (int)size);

    write_header(block, size, false);
    write_footer(block, size, false);

    coalesce(block);
    print_free_list();
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size) {
    block_t *block = payload_to_header(oldptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(oldptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (oldptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, oldptr, copysize);

    // Free the old block
    free(oldptr);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc (size_t nmemb, size_t size) {
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno) {
    return true;
}

/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size, block_t* prev_block)
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    dbg_printf("Extend heap.\n");
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    dbg_printf("Initialize free block header/footer.\n");
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);

    // Create new epilogue header
    dbg_printf("Create new epilogue header..\n");
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    dbg_printf("Coalesce\n");
    return coalesce(block);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, data));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    dbg_printf("[header_to_payload] block addr: %lx\n", (uint64_t)block);
    dbg_printf("[header_to_payload] data addr: %lx\n", (uint64_t)(&block->data));
    return (void *)(&(block->data));
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}


/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->data.payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}

static void link_blocks(block_t *prev, block_t* next)
{
    if (prev != NULL)
        prev->data.ptr.next = next;
    else
        free_list = next;
    if (next != NULL)
        next->data.ptr.prev = prev;
    else
        list_tail = prev;
}

static block_t* get_prev_free(block_t *block)
{
    return block->data.ptr.prev;
}

static block_t* get_next_free(block_t *block)
{
    return block->data.ptr.next;
}

static block_t* find_tail() {
    if (free_list == NULL)
        return NULL;
    block_t* block_iter;
    for (block_iter = free_list; get_next_free(block_iter) != NULL;
                             block_iter = get_next_free(block_iter));
    return block_iter;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    dbg_printf("[place] block addr: %p, size: %d csize: %d\n",
            (void*)block, (int)asize, (int)csize);

    if ((csize - asize) >= min_block_size)
    {
        dbg_printf("[place] Case 1\n");
        block_t *block_next;
        write_header(block, asize, true);
        write_footer(block, asize, true);

        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);

        link_blocks(get_prev_free(block), block_next);
        link_blocks(block_next, get_next_free(block));
    }

    else
    {
        dbg_printf("[place] Case 2\n");
        write_header(block, csize, true);
        write_footer(block, csize, true);
        link_blocks(get_prev_free(block), get_next_free(block));
    }
}

/*
 * find_fit: Looks for a free block with at least asize bytes with
 *           first-fit policy. Returns NULL if none is found.
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    dbg_printf("[find_fit] asize = %d\n", (int)asize);

    for (block = free_list; block != NULL; block = get_next_free(block))
    {
        dbg_printf("[find_fit] block addr: %p, block size: %d\n",
            (void*)block, (int)get_size(block));

        if (asize <= get_size(block))
        {
            return block;
        }
    }
    dbg_printf("[find_fit] NULL\n");
    return NULL; // no fit found
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | 1) : size;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}


/* Coalesce: Coalesces current block with previous and next blocks if either
 *           or both are unallocated; otherwise the block is not modified.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block)
{
    block_t *block_next = find_next(block);
    block_t *block_prev = find_prev(block);
    dbg_printf("[Coalesce]next: %p  prev: %p\n", (void*)block_next, (void*)block_prev);

    bool prev_alloc = extract_alloc(*(find_prev_footer(block)));
    bool next_alloc = get_alloc(block_next);
    dbg_printf("[Coalesce]next alloc: %d  prev alloc: %d\n", (int)next_alloc, (int)prev_alloc);
    size_t size = get_size(block);

    if (prev_alloc && next_alloc)              // Case 1
    {
        insert_to_free_list(block);
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        size += get_size(block_next);
        write_header(block, size, false);
        write_footer(block, size, false);
        link_blocks(block, get_next_free(block_next));
        link_blocks(get_prev_free(block_next), block);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        size += get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        block = block_prev;
    }

    else                                        // Case 4
    {
        size += get_size(block_next) + get_size(block_prev);
        write_header(block_prev, size, false);
        write_footer(block_prev, size, false);
        link_blocks(get_prev_free(block_next), get_next_free(block_next));
        // link_blocks(block_prev, get_next_free(block_next));

        block = block_prev;
    }
    return block;
}

static void insert_to_free_list(block_t *block)
{
    block_t *block_iter, *last_block;
    dbg_printf("[Insert to free list] %p\n", (void*)block);

    if (free_list == NULL) {
        link_blocks(NULL, block);
        link_blocks(block, NULL);
        return;
    }

    if (free_list > block) {
        link_blocks(block, free_list);
        link_blocks(NULL, block);
        return;
    }

    for (block_iter = free_list; block_iter != NULL;
                             block_iter = get_next_free(block_iter))
    {

        if (block_iter > block)
        {
            link_blocks(get_prev_free(block_iter), block);
            link_blocks(block, block_iter);
            return;
        }
        last_block = block_iter;
    }
    link_blocks(last_block, block);
    link_blocks(block, NULL);
}

static void print_free_list()
{
    dbg_printf("-----------------Free List------------------\n");
    block_t *block_iter;
    for (block_iter = free_list; block_iter != NULL;
            block_iter = get_next_free(block_iter))
    {
        dbg_printf("[Free list] block addr: %p, block size: %d prev: %p next: %p\n",
                (void*)block_iter, (int)get_size(block_iter),
                (void*)get_prev_free(block_iter), (void*)get_next_free(block_iter));
    }
    dbg_printf("-----------------Free List END------------------\n");
}
