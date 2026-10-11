-- Prove2me | Theorems.Thm_UnionFindAnalysis_find_amortized
-- name    : UnionFindAnalysis.find_amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:56:42.888734+00:00
-- url     : https://prove2.me/theorems/3dae1d37-dcea-4fe6-a531-f644a9168cbf
-- title:
--   Union-find: full-compression find and inverse-Ackermann running time
-- statement:
--   For a represented object and an in-range vertex, one actual terminating find returns its representative and supplies the final heap and compressed model together. The partition and ranks are unchanged, only the parent array may be written, and the exact measured increments satisfy
--   $$
--   W(\operatorname{Heap.cost}(before,after))+2\Phi(S_{after})
--   \le2\Phi(S_{before})+2\alpha(n)+3.
--   $$
--   The initial potential remains in this inequality: the theorem does not claim inverse-Ackermann worst-case time for an isolated find. It is designed for repeated calls using each returned model as the next input.
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
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find.lean#L643-L663

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_UnionFindAnalysis_find_contract
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.find_amortized :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (vertex : Fin n),
          Exists.{1} fun after =>
            Exists.{1} fun compressed =>
              Algo.union_find.UnionFind.find.Call heap
                  (Prod.mk.{0, 0} layout.object (↑(↑vertex : Nat) : Int)) after
                  (↑(↑(model.representative vertex) : Nat) : Int) ∧
                UnionFindAnalysis.Rep after layout compressed ∧
                  Eq.{1} compressed.representative model.representative ∧
                    Eq.{1} compressed.rank model.rank ∧
                      UnionFindAnalysis.Storage heap after (List.cons.{0} layout.parent List.nil.{0}) ∧
                        heap.Increments after (heap.cost after) ∧
                          LE.le.{0}
                            (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work (heap.cost after))
                              (HMul.hMul.{0, 0, 0} (2 : Nat)
                                (Algo2Lean.UnionFind.potential compressed)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model))
                                (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.Ackermann.alpha n)))
                              (3 : Nat)) := by
  sorry
