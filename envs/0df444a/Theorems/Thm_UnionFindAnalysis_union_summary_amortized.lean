-- Prove2me | Theorems.Thm_UnionFindAnalysis_union_summary_amortized
-- name    : UnionFindAnalysis.union_summary_amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:00:42.148356+00:00
-- url     : https://prove2.me/theorems/95336750-01dc-4766-b153-5a4c1a939ee5
-- title:
--   Union-find: reusable union contract with inverse-Ackermann running time
-- statement:
--   For a represented object and in-range vertices $a,b$, one terminating union call returns whether the old components differ and supplies the next representation. Its new connectivity is exactly the old relation with those two components joined. Only parent/rank arrays can be written, no unrelated storage is changed, and clocks outside `uf_find`, `uf_compress`, `uf_union` stay fixed.
--
--   For the actual before/after heaps and corresponding models, the contract gives both
--   $$
--   W_{after}\le W_{before}+4\lfloor\log_2 n\rfloor+3
--   $$
--   and
--   $$
--   W_{after}+2\Phi(S_{after})\le W_{before}+2\Phi(S_{before})+6\alpha(n)+7.
--   $$
--   The second bound retains the initial potential and is amortized, not an inverse-Ackermann worst-case bound on one call. Kruskal's scan consumes this exact same-model contract.
--
--   The precondition `Rep heap layout model` connects an allocated object and distinct allocated parent/rank arrays to a valid forest on `Fin n`. Validity includes representative consistency, strictly increasing rank along nonroot parent links, and the root-mass rank bound. It does not assume a particular operation history. Vertex arguments belong to `Fin n`; no such argument exists when $n=0$.
--
--   For compiled calls, $W$ sums `uf_init`, `uf_find`, `uf_compress`, and `uf_union` with unit weights. A find changes only the two find/compression clocks; a union adds those events and one union tick. Initialization is charged by the constructor.
--
--   Here $n$ is the fixed number of elements, $\alpha(n)$ is `Algo2Lean.Ackermann.alpha`, and $\Phi$ is `Algo2Lean.UnionFind.potential`. Their definitions are in the separate Ackermann and union-find amortization definition bundles. The inverse is the least positive $k$ with $A_k(1)>n$, where $A_0(r)=r+1$ and $A_{k+1}(r)$ iterates $A_k$ exactly $r+1$ times starting at $r$.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find.lean#L665-L702

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_UnionFindAnalysis_union_contract
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_potential
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.union_summary_amortized :
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
                    heap.Footprint after
                        (List.cons.{0} layout.parent (List.cons.{0} layout.rank List.nil.{0}))
                        List.nil.{0} List.nil.{0} ∧
                      (∀ (clock : String),
                          ¬Membership.mem.{0, 0}
                                (List.cons.{0} "uf_find"
                                  (List.cons.{0} "uf_compress" (List.cons.{0} "uf_union" List.nil.{0})))
                                clock →
                            Eq.{1} (after.clocks clock) (heap.clocks clock)) ∧
                        LE.le.{0} (UnionFindAnalysis.work after.clocks)
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work heap.clocks)
                                (HMul.hMul.{0, 0, 0} (4 : Nat) n.log2))
                              (3 : Nat)) ∧
                          LE.le.{0}
                            (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work after.clocks)
                              (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential nextModel)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (UnionFindAnalysis.work heap.clocks)
                                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model)))
                                (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n)))
                              (7 : Nat)) := by
  sorry
