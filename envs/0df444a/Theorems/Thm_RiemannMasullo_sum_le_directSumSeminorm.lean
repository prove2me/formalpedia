-- Prove2me | Theorems.Thm_RiemannMasullo_sum_le_directSumSeminorm
-- name    : RiemannMasullo.sum_le_directSumSeminorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:26:01.839675+00:00
-- url     : https://prove2.me/theorems/b36cb2c6-8f66-4dd7-bfd7-274697f0b778
-- title:
--   Finite partial sums of coordinate seminorms
-- statement:
--   For any vector in an algebraic direct sum and any finite set of indices, the partial sum of the coordinate seminorms is bounded above by the direct-sum seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L40-L44

import Definitions.Def_RiemannMasullo_DirectSumSeminorm

open scoped DirectSum
open RiemannMasullo
variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

namespace RiemannMasullo

theorem sum_le_directSumSeminorm (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i)
    (s : Finset ι) : (∑ i ∈ s, p i (x i)) ≤ directSumSeminorm p x := by sorry

end RiemannMasullo
