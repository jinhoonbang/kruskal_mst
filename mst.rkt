;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname mst) (read-case-sensitive #t) (teachpacks ((lib "image.rkt" "teachpack" "2htdp"))) (htdp-settings #(#t quasiquote repeating-decimal #t #t none #f ((lib "image.rkt" "teachpack" "2htdp")) #f)))
#|
|#
;;;;WEIGHTED, UNDIRECTED GRAPHS ;;;;

;; Vertex is N

;; Weight is Number

;; A MaybeWeight is one of:
;; -- Weight
;; -- +inf.0
;; Interpretation: the weight of an edge may be a number or infinite
;; (which means no edge)

;; A WUGraph is (make-WUGraph N [Vector-of (make-MatrixRow Vector-of X)])
;; WUGraph is represented as an adjacency matrix.
;; WUGraph's size is number of vertices
;; WUGraph's matrix is a vector of MatrixRow.
;; MatrixRow is a vector.
;; In other words, WUGraph's matrix is vector of vectors, in which
;; (row number, column number) represents edges and each element
;; represents the weight associated with the corresponding edge.
;; Indices 0 to N - 1 is used to access elements in WUGraph's matrix

(define-struct WUGraph [size matrix])
(define-struct MatrixRow [row])

;; make-graph : N -> WUGraph
;; Creates a new weighted, undirected graph with n vertices and no
;; edges.
(define (make-graph n)
  (make-WUGraph n (build-vector n (lambda (index) (make-vector n +inf.0)))))

;; graph-size : WUGraph -> N
;; Returns the number of vertices in the graph.
(define (graph-size g)
  (WUGraph-size g))


;; get-edge : WUGraph Vertex Vertex -> MaybeWeight
;; Gets the weight of the edge from v to u, or infinity if there
;; is no such edge.
;;
;; For any g, v, and u, it ought to be the case that
;;   (= (get-edge g v u) (get-edge g u v))
; check for valikd v u?
(define (get-edge g v u)
  (vector-ref (vector-ref (WUGraph-matrix g) v) u))

;;set-edge! : WUGraph Vertex Vertex MaybeWeight -> Void
(define (set-edge! g u v weight)
  (begin
    (vector-set! (vector-ref (WUGraph-matrix g) u) v weight)
    (vector-set! (vector-ref (WUGraph-matrix g) v) u weight)))

;id-adjacent? : checks if given v is +inf.0?
(define (is-adjacent? v)
  (if (equal? v +inf.0)
      #false
      #true))
      
(define (get-adjacent g v)
  (local
    [(define temp null)
     (define (add-adj i)
       (when (< i (graph-size g))
           (if (is-adjacent? (get-edge g v i))
               (begin
                 (set! temp (append temp (list i)))
                 (add-adj (+ i 1)))
               (add-adj (+ i 1)))))]
    (begin
      (add-adj 0)
      temp)))

;;;;Binary Heap;;;;

; A [Maybe X] is one of:
; -- X
; -- #false
; Interpretation: maybe an X, or maybe not

; An [Ord X] is a function [X X -> Boolean]
; Interpretation: a total order on X

; A [Heap X] is (make-heap N [Ord X] [Vector-of X])
(define-struct heap [size lt? data])

;
; Interpretation: Given a heap h,
; - (heap-size h) is the number of elements in the heap
; - (heap-lt? h) is the ordering used by the heap
; - (heap-data h) is a vector containing the heap's elements, where the
;   first (heap-size h) elements are an implicit complete binary tree (i.e.,
;   they contain the in-order traversal of the represented tree as we saw
;   in class.
;
; Invariant: The implicit tree satisfies the min-heap property; that is,
; if c is the index of some node and p is the index of its parent then
;    ((heap-lt? h) p c)
; must be true.

; create : N [Ord X] -> [Heap X]
; Creates a new heap with capacity `capacity` and order `lt?`.
(define (create-BinHeap capacity lt?)
  (make-heap 0 lt? (make-vector capacity #false)))

;function that doubles vector size and copies the content of the old vector
(define (duplicate-vector heap)
  (local
    [(define temp (make-vector (max 1 (* 2 (vector-length (heap-data heap)))) #false))
    (define (copy! src dest i)
      (if (< i 0)
      (void)
      (begin
        (vector-set! dest i (heap-ref src i))
        (copy! src dest (- i 1)))))]
      ;(vector-copy! temp 0 (heap-data heap))
    (begin
      (copy! heap temp (- (heap-size heap) 1))
      (set-heap-data! heap temp))))
      
; insert! : [Heap X] X -> Void
; Adds an element to a heap.
; Error if the heap has reached capacity and cannot grow further.
(define (insert! heap new-element)
  (if (< (heap-size heap) (vector-length (heap-data heap)))
      (begin
        (heap-set! heap (heap-size heap) new-element)
        (bubble-up! heap (heap-size heap))
        (set-heap-size! heap (+ (heap-size heap) 1)))
      (begin
        (duplicate-vector heap)
        (heap-set! heap (heap-size heap) new-element)
        (bubble-up! heap (heap-size heap))
        (set-heap-size! heap (+ (heap-size heap) 1)))))

; find-min : [Heap X] -> X
; Returns the least element in the heap.
; Error if the heap is empty.
(define (find-min heap)
  (if (> (heap-size heap) 0)
      (heap-ref heap 0)
      (error "The heap is empty")))

; remove-min! : [Heap X] -> Void
; Removes the least element in the heap.
; Error if the heap is empty.
(define (remove-min! heap)
  (if (> (heap-size heap) 0)
      (begin
        (swap! heap 0 (- (heap-size heap) 1))
        (heap-set! heap (- (heap-size heap) 1) #false)
        (set-heap-size! heap (- (heap-size heap) 1))
        (percolate-down! heap 0))
      (error "The heap is empty")))

;;;; PRIVATE HELPERS

; A [Maybe X] is one of:
; -- #false
; -- X
; Interpretation: maybe an X, or maybe not

; heap:ensure-size! : [Heap X] N -> Void
; Ensures that the heap has room for `size` elements by throwing an error
; if it doesn't.

(define (ensure-size! heap n)
  (if (> n (heap-size heap))
      (error "not enough room in the heap")
      (void)))
  
  
; heap:percolate-down! : [Heap X] N -> Void
; Restores the heap invariant by percolating down, starting with the element
; at `index`.
(define (percolate-down! heap i)
  (local
    [(define temp 0)
     (define (local-percolate! heap i)
       (if (number? (find-smaller-child heap i)) 
           (if (lt? heap i (find-smaller-child heap i))
               (void)
               (begin
                 (set! temp (find-smaller-child heap i))
                 (swap! heap i temp)
                 (if (number? (find-smaller-child heap temp))
                 (local-percolate! heap temp)
                 (void))))
       (void)))]
    (local-percolate! heap i)))
       

; heap:find-smaller-child : [Heap X] N -> [Maybe N]
; Finds the index of the smaller child of node `index`, or `#false` if
; it has no children.
(define (find-smaller-child heap i)
      (if (< (left i) (heap-size heap))
          (if (< (right i) (heap-size heap))
              (if (lt? heap (left i) (right i))
                  (left i)
                  (right i))
              (left i))
          #false))

; heap:bubble-up! : [Heap X] N -> Void
; Restores the heap invariant by bubbling up the element at `index`.
(define (bubble-up! heap i)
  (local
    [(define (local-bubble! heap i)
       (if (> i 0)
           (if (lt? heap i (parent i))
               (begin
                 (swap! heap i (parent i))
                 (local-bubble! heap (parent i)))
               (void))
           (void)))]
  (local-bubble! heap i)))

; heap:ref : [Heap X] N -> X
; Gets the heap element at `index`.
(define (heap-ref heap i)
  (vector-ref (heap-data heap) i)) 

; heap:set! : [Heap X] N X -> Void
; Sets the heap element at `index`.
(define (heap-set! heap i x)
  (vector-set! (heap-data heap) i x)) 

; heap:swap! : [Heap X] N N -> Void
; Swaps the heap elements at indices `i` and `j`.
(define (swap! heap i j)
  (local
    [(define temp (heap-ref heap i))]
    (begin
      (heap-set! heap i (heap-ref heap j))
      (heap-set! heap j temp))))

; heap:lt? : [Heap X] N N -> Boolean
; Returns whether the element at `i` is less than the element at `j`
; using the heap's order.
(define (lt? heap i j)
  (if ((heap-lt? heap) (heap-ref heap i) (heap-ref heap j)) #true #false))   
  
  
; N is the set of natural numbers
; N+ is the set of positive integers

; heap:left : N -> N+
; Computes the index of the left child of the given index.
(define (left index)
  (+ (* index 2) 1))

; heap:right : N -> N+
; Computes the index of the left child of the given index.
(define (right index)
  (+ (* index 2) 2))

; heap:parent : N+ -> N
; Computes the index of the parent of the given index.
(define (parent index)
  (floor (/ (- index 1) 2)))

;;;;Union Find;;;;

; A UnionFind (represented as 'uf') is a struct with two fields: 'size', a fixed variable that
; stores the number objects and 'data', an ASL vector of UnionFindElements (represented as 'ufe').
; A UnionFindElement is a struct with two fieds: 'parent', the parent of the corresponding index
; and 'weight', the weight of the corresponding index. 
(define-struct ufe [parent weight])
(define-struct uf [size data])

(define (initialize index)
  (make-ufe index 1))

; create : N -> UnionFind
; Creates a new union-find structure having `size` initially-disjoint
; sets numbered 0 through `(- size 1)`.
(define (create-UF size)
  (make-uf size (build-vector size initialize)))

; size : UnionFind -> N
; Returns the number of objects in `uf`.
(define (size uf)
  (uf-size uf))

; same-set? : UnionFind N N -> Boolean
; Returns whether objects `obj1` and `obj2` are in the same set.
(define (same-set? uf obj1 obj2)
  (if (= (find uf obj1) (find uf obj2))
      #true
      #false))

; find : UnionFind N -> N
; Finds the representative (root) object for `obj`.
(define (find uf obj)
  (local
    [(define (local-root! uf obj)
     (if (= obj (ufe-parent (uf:get-entry uf obj)))
         (ufe-parent (uf:get-entry uf obj))
         (begin
           (set-ufe-parent! (uf:get-entry uf obj) (local-root! uf (ufe-parent (uf:get-entry uf obj))))
           (ufe-parent (uf:get-entry uf obj)))))]
    (local-root! uf obj)))

; union : UnionFind N N -> Void
; Unions the set containing `obj1` with the set containing `obj2`.
(define (union! uf obj1 obj2)
  (local
    [(define root-obj1 (uf:get-entry uf (find uf obj1)))
     (define root-obj2 (uf:get-entry uf (find uf obj2)))]
    (if (= obj1 obj2)
        (void)
        (if (> (ufe-weight root-obj1) (ufe-weight root-obj2))
            (uf:reparent! uf root-obj2 root-obj1)
            (uf:reparent! uf root-obj1 root-obj2)))))

; uf:reparent! : UnionFindEntry UnionFindEntry -> Void
; Sets the parent of `child` to be `parent` and adjusts `parent`’s
; weight accordingly.
(define (uf:reparent! uf child parent)
  (begin
    (set-ufe-parent! child (ufe-parent parent))
    (set-ufe-weight! parent (+ (ufe-weight child) (ufe-weight parent))))) 

; uf:get-entry : UnionFind N -> UnionFindEntry
; Gets the entry for object `ix`.
(define (uf:get-entry uf ix)
   (vector-ref (uf-data uf) ix))

;;;;; KRUSKAL’S ALGORITHM ;;;;
;
;;; kruskal-mst : WUGraph -> WUGraph
;;; Returns the minimum spanning forest for a given graph, represented as
;;; another graph.
(define (kruskal-mst g)
  (local
    [(define ordered-edges (get-all-edges/increasing g))
     (define n-vertices (graph-size g))
     (define mst (make-graph n-vertices))
     (define unionfind (create-UF n-vertices))
     (define (local-add-edge)
       (when (not (null? ordered-edges))
         (if (same-set? unionfind (car (car ordered-edges)) (car (cdr (car ordered-edges))))
             (begin
               (set! ordered-edges (cdr ordered-edges))
               (local-add-edge))
             (begin
               (union! unionfind (car (car ordered-edges)) (car (cdr (car ordered-edges))))
               (set-edge! mst (car (car ordered-edges)) (car (cdr (car ordered-edges))) (get-edge g (car (car ordered-edges)) (car (cdr (car ordered-edges)))))  
               (set! ordered-edges (cdr ordered-edges))
               (local-add-edge)))))]
    (begin
      (local-add-edge)
      mst)))
   
;;; get-all-edges/increasing : WUGraph -> [List-of (list Vertex Vertex)]
;;; Gets a list of all the edges in the graph sorted by increasing weight;
;;; includes only one (arbitrary) direction for each edge.
(define (get-all-edges/increasing g)
  (local
    [(define all-edges (get-all-edges g))
     (define ordered-edges null)
     (define (edge-lt? a b)
      (if (< (get-edge g (car a) (car (cdr a))) (get-edge g (car b) (car (cdr b))))
          #true
          #false))
     (define binheap (create-BinHeap (length all-edges) edge-lt?))
     (define (local-insert!)
       (when (not (null? all-edges))
         (begin
           (insert! binheap (car all-edges))
           (set! all-edges (remove (car all-edges) all-edges))
           (local-insert!))))
    (define (local-append)
      (when (< (length ordered-edges) (vector-length (heap-data binheap)))
        (begin
          (set! ordered-edges (append ordered-edges (list (pq-extract-min! binheap))))
          (local-append))))]
    (begin
      (local-insert!)
      (local-append)
      ordered-edges)))
      
;;; get-all-edges : WUGraph -> [List-of (list Vertex Vertex)]
;;; Gets all the edges in a graph as a list of 2-element lists; includes
;;; only one (arbitrary) direction for each edge.
(define (get-all-edges g)
  (local
    [(define N (graph-size g))
     (define edge-list null)
     (define temp null)
     (define (add-one i)
                (when (not (null? temp))
                  (if (or (member? (list i (car temp)) edge-list) (member? (list (car temp) i) edge-list))
                      (begin
                        (set! temp (remove (car temp) temp))
                        (add-one i))
                      (begin
                        (set! edge-list (append edge-list (list (list (car temp) i))))
                        (set! temp (remove (car temp) temp))
                        (add-one i)))))
     (define (add-edge i)
       (when (< i N)
         (begin
           (set! temp (get-adjacent g i))
           (add-one i)
           (add-edge (+ i 1)))))]
    (begin
      (add-edge 0)
      edge-list)))
;;; heap-sort : [Ord X] [List-of X] -> [List-of X]
;;; Sorts a list based on the given less-than function.
;(define (heap-sort lt? xs)
;  ...)

;;; pq-extract-min! : [Heap X] -> X
;;; Removes and returns the minimum heap element.
(define (pq-extract-min! heap)
  (local
    [(define min (find-min heap))]
    (begin
      (remove-min! heap)
      min)))

;;;; TESTING

;; The following function may be convenient for creating graphs for
;; tests. It uses the graph API that you are defining above, so if you
;; define make-graph and set-edge! correctly then it will work.

;; build-graph : N [List-of (list Vertex Vertex Weight)] -> WUGraph
;; Returns a new graph of n vertices containing the given edges.
(define (build-graph n edges)
  (local [(define new-graph (make-graph n))]
    (begin
      (map (lambda (edge)
             (set-edge! new-graph (first edge) (second edge) (third edge)))
           edges)
      new-graph)))

(define EXAMPLE-GRAPH-0
  (build-graph 6
               '((0 1 5)
                 (0 2 7)
                 (0 3 2)
                 (1 4 9)
                 (1 5 6)
                 (3 5 0)
                 (3 4 1))))

(check-expect (graph-size EXAMPLE-GRAPH-0) 6)
(check-expect (get-edge EXAMPLE-GRAPH-0 0 1) 5)
(check-expect (get-edge EXAMPLE-GRAPH-0 1 0) 5)
(check-expect (get-edge EXAMPLE-GRAPH-0 0 2) 7)
(check-expect (get-edge EXAMPLE-GRAPH-0 2 0) 7)
(check-expect (get-edge EXAMPLE-GRAPH-0 3 5) 0)
(check-expect (get-edge EXAMPLE-GRAPH-0 5 3) 0)

;; check-expect doesn’t like comparing +inf.0, so we can just do
;; the comparison manually:
(check-expect (= +inf.0 (get-edge EXAMPLE-GRAPH-0 0 4)) #true)
(check-expect (= +inf.0 (get-edge EXAMPLE-GRAPH-0 4 0)) #true)

;; Note that my get-adjacent returns a sorted list, but yours doesn’t
;; need to---and if it doesn’t then you will have to modify these tests.
(check-expect (get-adjacent EXAMPLE-GRAPH-0 0) '(1 2 3))
(check-expect (get-adjacent EXAMPLE-GRAPH-0 1) '(0 4 5))
(check-expect (get-adjacent EXAMPLE-GRAPH-0 5) '(1 3))

;; This graph looks like a "wagon wheel" with six spokes emanating from
;; vertex 6 in the center. The weights of the spokes are mostly less
;; than the weights along the perimeter, except that 3 is closer to 2
;; than it is to 6. Thus, the resulting MST is all spokes except that it
;; connects 3 to 2 rather than to 6.
(define EXAMPLE-GRAPH-1
  (build-graph 7
               '((0 1 3)
                 (1 2 3)
                 (2 3 1)
                 (3 4 3)
                 (4 5 3)
                 (6 0 2)
                 (6 1 2)
                 (6 2 2)
                 (6 3 3)
                 (6 4 2)
                 (6 5 2))))

(define EXAMPLE-MST-1 (kruskal-mst EXAMPLE-GRAPH-1))

(check-expect (get-adjacent EXAMPLE-MST-1 0) '(6))
(check-expect (get-adjacent EXAMPLE-MST-1 1) '(6))
(check-expect (get-adjacent EXAMPLE-MST-1 2) '(3 6))
(check-expect (get-adjacent EXAMPLE-MST-1 3) '(2))
(check-expect (get-adjacent EXAMPLE-MST-1 4) '(6))
(check-expect (get-adjacent EXAMPLE-MST-1 5) '(6))
(check-expect (get-adjacent EXAMPLE-MST-1 6) '(0 1 2 4 5))

(define EXAMPLE-GRAPH-2
  (build-graph 5
               '((0 1 4)
                 (0 2 3)
                 (0 4 7)
                 (1 2 2)
                 (0 3 10)
                 (1 3 5)
                 (2 4 15)
                 (3 4 4)
                 (2 3 4))))

(define EXAMPLE-MST-2 (kruskal-mst EXAMPLE-GRAPH-2))

(check-expect (get-adjacent EXAMPLE-MST-2 0) '(2))
(check-expect (get-adjacent EXAMPLE-MST-2 1) '(2))
(check-expect (get-adjacent EXAMPLE-MST-2 2) '(0 1 3))
(check-expect (get-adjacent EXAMPLE-MST-2 3) '(2 4))
(check-expect (get-adjacent EXAMPLE-MST-2 4) '(3))
