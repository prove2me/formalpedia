-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_1_10
-- name    : SparseDisc.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:10:36.759421+00:00
-- url     : https://prove2.me/theorems/ffb19a2f-51c7-424a-8a22-c25ce43658ec
-- title:
--   Theorem 1.10 — thin shared bundles
-- statement:
--   Let $F$ be a finite $2$-sparse family of $n$ functions such that any two functions share at most $s$ relevant items. Then
--   $$
--   \operatorname{disc}(F)\le1+2\left\lceil\sqrt{sn/2}\right\rceil.
--   $$
--   If the item multigraph is simple, in particular for $K_n$ with single-item bundles, then $\operatorname{disc}(F)\le\sqrt{2n}+3$. More generally, a $t$-sparse family under the same pairwise cap satisfies
--   $$
--   \operatorname{disc}(F)\le1+2s\sqrt{t(t-1)n}.
--   $$
--
--   Differences from the source:
--   - encoding: $n$ functions and pairwise shared relevant items → `n` is the cardinality of a finite function type and intersections of published relevance supports have cardinality at most `s`; reason: Lean convention, with the same families
--   - reading: the item multigraph is simple → every pair of relevance supports intersects in at most one item; reason: in a 2-sparse family this is exactly absence of parallel non-private item edges
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 1.10, p.5

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_relevant
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_Supplement_IsTSparse
import Definitions.Def_SparseDisc_Supplement_PairwiseSharedCap

namespace SparseDisc.Supplement

/-- **Theorem 1.10** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.5). Pairwise shared-item cap `s` gives the
exact `2`-sparse ceiling bound, its simple-item-multigraph consequence, and the general
`t`-sparse bound. -/
theorem theorem_1_10 :
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ) (s : ℕ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f →
      PairwiseSharedCap (fun v => SparseDisc.relevant (f v)) s →
      SparseDisc.DiscLE f
        (1 + 2 * ((Nat.ceil (Real.sqrt (((s * Fintype.card V : ℕ) : ℝ) / 2)) : ℕ) : ℝ))) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f →
      PairwiseSharedCap (fun v => SparseDisc.relevant (f v)) 1 →
      SparseDisc.DiscLE f (Real.sqrt (2 * Fintype.card V) + 3)) ∧
    (∀ (t s : ℕ), 1 ≤ t → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ),
      (∀ v, SparseDisc.IsOneLipschitz (f v)) → IsTSparse t f →
      PairwiseSharedCap (fun v => SparseDisc.relevant (f v)) s →
      SparseDisc.DiscLE f
        (1 + 2 * s * Real.sqrt ((t * (t - 1) * Fintype.card V : ℕ) : ℝ))) := by sorry

end SparseDisc.Supplement
