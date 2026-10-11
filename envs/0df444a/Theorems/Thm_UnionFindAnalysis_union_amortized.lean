-- Prove2me | Theorems.Thm_UnionFindAnalysis_union_amortized
-- name    : UnionFindAnalysis.union_amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:00:45.298975+00:00
-- url     : https://prove2.me/theorems/150f3189-665b-4c46-b0e2-5d13d13c54e9
-- title:
--   Union-find: union by rank and inverse-Ackermann running time
-- statement:
--   For a represented object and in-range vertices $a,b$, a terminating union returns true exactly when their original representatives differ. The next model joins exactly those two old components: two vertices are connected afterward precisely when they were already connected or lie on opposite sides of that component pair. The same call preserves all storage outside the parent/rank arrays, allocates no storage and supplies exact clock increments.
--
--   Its measured work satisfies
--   $$
--   W(\operatorname{Heap.cost}(before,after))+2\Phi(S_{after})
--   \le2\Phi(S_{before})+6\alpha(n)+7.
--   $$
--   This is an amortized contract with a retained potential, not an individual worst-case bound on work alone. It is independent of Kruskal and can be composed by future clients carrying the returned representation forward.
--
--   The precondition `Rep heap layout model` connects an allocated object and distinct allocated parent/rank arrays to a valid forest on `Fin n`. Validity includes representative consistency, strictly increasing rank along nonroot parent links, and the root-mass rank bound. It does not assume a particular operation history. Vertex arguments belong to `Fin n`; no such argument exists when $n=0$.
--
--   For compiled calls, $W$ sums `uf_init`, `uf_find`, `uf_compress`, and `uf_union` with unit weights. A find changes only the two find/compression clocks; a union adds those events and one union tick. Initialization is charged by the constructor.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   This result belongs to the [Algo2Lean](https://www.algo2lean.com/) CLRS series, corresponding to *Introduction to Algorithms*, fourth edition, Chapter 19, §§19.3–19.4, especially the inverse-Ackermann analysis of Theorem 19.14. The API initializes a fixed universe in one constructor rather than interleaving individual MAKE-SET operations.
--
--   ## Algorithm source
--
--   Project import root: `examples/kruskal`. Entry file: `union_find.algo`.
--
--   ### `union_find.algo`
--
--   ```python
--   # Disjoint sets over the integer elements 0, ..., size - 1.
--   # Each root names one component. Union by rank bounds parent paths, and
--   # find compresses every visited path directly to its root.
--   # Clients must pass in-range elements. The representation is independent
--   # of graphs, edge weights, or any particular client algorithm.
--
--   class UnionFind:
--       parent: Seq
--       rank: Seq
--       size: Int
--
--       def __init__(self, size: Int) -> None:
--           # Batch the CLRS MAKE-SET operation for all elements in [0, size).
--           self.parent = const(0)
--           self.rank = const(0)
--           self.size = size
--           vertex = 0
--           tick("uf_init")
--           # @initialize
--           while vertex < size:
--               self.parent[vertex] = vertex
--               vertex += 1
--               tick("uf_init")
--
--       def find(self, vertex: Int) -> Int:
--           # CLRS FIND-SET: recursion finds the root, then rewrites every parent
--           # along the return path. This is full path compression, not path halving.
--           parent = self.parent
--           tick("uf_find")
--           # @follow
--           if parent[vertex] == vertex:
--               return vertex
--           root = self.find(parent[vertex])
--           # @compress
--           parent[vertex] = root
--           tick("uf_compress")
--           return root
--
--       def union(self, a: Int, b: Int) -> Bool:
--           # CLRS UNION: find both roots, then apply union by rank (LINK).
--           # The Boolean result reports whether two components were joined.
--           left = self.find(a)
--           right = self.find(b)
--           tick("uf_union")
--           if left == right:
--               return False
--           # @link
--           if self.rank[left] < self.rank[right]:
--               self.parent[left] = right
--           elif self.rank[right] < self.rank[left]:
--               self.parent[right] = left
--           else:
--               # Equal ranks may choose either root; here the left root wins.
--               self.parent[right] = left
--               self.rank[left] = self.rank[left] + 1
--           return True
--   ```
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find.lean#L705-L728

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_UnionFindAnalysis_union_contract
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_potential
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.union_amortized :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (a b : Fin n),
          Exists.{1} fun after =>
            Exists.{1} fun nextModel =>
              Algo.union_find.UnionFind.union.Call heap
                  (Prod.mk.{0, 0} layout.object
                    (Prod.mk.{0, 0} (↑(↑a : Nat) : Int) (↑(↑b : Nat) : Int)))
                  after (Decidable.decide (Ne.{1} (model.representative a) (model.representative b))) ∧
                UnionFindAnalysis.Rep after layout nextModel ∧
                  (∀ (x y : Fin n),
                      Algo2Lean.UnionFind.Connected nextModel x y ↔
                        Algo2Lean.UnionFind.Connected model x y ∨
                          Algo2Lean.UnionFind.Connected model x a ∧
                              Algo2Lean.UnionFind.Connected model y b ∨
                            Algo2Lean.UnionFind.Connected model x b ∧
                              Algo2Lean.UnionFind.Connected model y a) ∧
                    UnionFindAnalysis.Storage heap after
                        (List.cons.{0} layout.parent (List.cons.{0} layout.rank List.nil.{0})) ∧
                      heap.Increments after (heap.cost after) ∧
                        LE.le.{0}
                          (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work (heap.cost after))
                            (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential nextModel)))
                          (HAdd.hAdd.{0, 0, 0}
                            (HAdd.hAdd.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model))
                              (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n)))
                            (7 : Nat)) := by
  sorry
