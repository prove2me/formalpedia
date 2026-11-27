-- Prove2me | Theorems.Thm_PvsNP_StreamReductionRank_accepting_target_code_bounds_residuals
-- name    : PvsNP.StreamReductionRank.accepting_target_code_bounds_residuals
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T05:26:23.501811+00:00
-- url     : https://prove2.me/theorems/38cf13f7-214b-5144-93a4-4d04753b8d93
-- title:
--   Accepting target codes bound the residual rank of a streaming reduction
-- statement:
--   Suppose a correct streaming reduction has a finite family of source prefixes that have accepting completions and are pairwise distinguishable by suffixes. A finite summary recovers the state at the cut. Each accepting target is decoded by a finite code and has length at most L. The number of source prefixes is at most the product of the numbers of summaries and codes and L+1, even if the reduction is noninjective and its output length varies.
-- source:
--   Residual counting for transfers to succinct problems with sparse accepting sets.

import Definitions.Def_StreamReductionResidualRank

set_option autoImplicit false

open PvsNP.StreamReductionRank

universe u v w x y

theorem PvsNP.StreamReductionRank.accepting_target_code_bounds_residuals {A : Type u} {B : Type v} {S : Type w} {I : Type x} {Code : Type y} {Summary : Type*}
    [Fintype I] [Fintype Summary] [Fintype Code]
    (R : Transducer A B S) (initialWord : I → List A)
    (remember : I → Summary)
    (faithful : ∀ i j, remember i = remember j →
      (R.run R.init (initialWord i)).1 = (R.run R.init (initialWord j)).1)
    (source : List A → Prop) (target : List B → Prop)
    (decode : Code → List B) (limit : ℕ)
    (width : ∀ c, (decode c).length ≤ limit)
    (complete : ∀ i, ∃ tail, source (initialWord i ++ tail))
    (separate : ∀ i j, i ≠ j → ∃ tail, ¬ (source (initialWord i ++ tail) ↔ source (initialWord j ++ tail)))
    (correct : ∀ i tail, target (R.output (initialWord i ++ tail)) ↔ source (initialWord i ++ tail))
    (covers : ∀ z, target z → ∃ c, decode c = z) :
    Fintype.card I ≤ Fintype.card Summary * Fintype.card Code * (limit+1) := by sorry
