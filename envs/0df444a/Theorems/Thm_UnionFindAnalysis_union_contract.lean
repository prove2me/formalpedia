-- Prove2me | Theorems.Thm_UnionFindAnalysis_union_contract
-- name    : UnionFindAnalysis.union_contract
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:55:29.944983+00:00
-- url     : https://prove2.me/theorems/8cc6b81e-37e1-4dbd-b707-c3876e651c26
-- title:
--   Union-find: exact mutable union contract
-- statement:
--   A represented union-find object admits a terminating `UnionFind.union.Call` for any two in-range vertices $a,b$. The Boolean result is true exactly when their representatives differed in the initial model. The theorem exposes witnesses for the two traversed paths, the two compression results and rank link, the corresponding final model, exact clock increments, and storage preservation outside the parent/rank arrays.
--
--   If the two path lengths are $p$ and $q$, `unionCosts p q` charges $p+q+2$ `uf_find` ticks, $p+q$ `uf_compress` ticks and one `uf_union` tick; every other clock has increment zero. This is the exact operational basis for the later amortized theorem.
--
--   The precondition `Rep heap layout model` connects an allocated object and distinct allocated parent/rank arrays to a valid forest on `Fin n`. Validity includes representative consistency, strictly increasing rank along nonroot parent links, and the root-mass rank bound. It does not assume a particular operation history. Vertex arguments belong to `Fin n`; no such argument exists when $n=0$.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/union_find.lean#L538-L581

import Definitions.Def_Algo_union_find_Analysis
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_valid

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem UnionFindAnalysis.union_contract :
    ∀ {n : Nat} (heap : Algo2LeanGenerated.Heap) (layout : UnionFindAnalysis.Layout)
      (model : Algo2Lean.UnionFind.State n),
      UnionFindAnalysis.Rep heap layout model →
        ∀ (a b : Fin n),
          Exists.{1} fun first =>
            Exists.{1} fun second =>
              Exists.{1} fun after =>
                Algo2Lean.UnionFind.Find model a (model.representative a) first ∧
                  Algo2Lean.UnionFind.Find (UnionFindAnalysis.findResult model a first) b
                      ((UnionFindAnalysis.findResult model a first).representative b) second ∧
                    Algo.union_find.UnionFind.union.Call heap
                        (Prod.mk.{0, 0} layout.object
                          (Prod.mk.{0, 0} (↑(↑a : Nat) : Int) (↑(↑b : Nat) : Int)))
                        after
                        (Decidable.decide (Ne.{1} (model.representative a) (model.representative b))) ∧
                      UnionFindAnalysis.Rep after layout
                          (UnionFindAnalysis.unionResult model a b first second) ∧
                        UnionFindAnalysis.Storage heap after
                            (List.cons.{0} layout.parent (List.cons.{0} layout.rank List.nil.{0})) ∧
                          heap.Increments after (UnionFindAnalysis.unionCosts first second) := by
  sorry
