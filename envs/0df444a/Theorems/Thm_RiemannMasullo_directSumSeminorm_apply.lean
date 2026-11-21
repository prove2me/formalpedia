-- Prove2me | Theorems.Thm_RiemannMasullo_directSumSeminorm_apply
-- name    : RiemannMasullo.directSumSeminorm_apply
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:26:02.794944+00:00
-- url     : https://prove2.me/theorems/29ad87d1-c21a-4ab3-a8c4-d12fe648275e
-- title:
--   Finite evaluation of the direct-sum seminorm
-- statement:
--   The direct-sum seminorm equals the sum of the coordinate seminorms over any finite set containing the support of the given vector.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L28-L31

import Definitions.Def_RiemannMasullo_DirectSumSeminorm

open scoped DirectSum
open RiemannMasullo
variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

namespace RiemannMasullo

theorem directSumSeminorm_apply (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i) (s : Finset ι)
    (hs : x.support ⊆ s) :
    directSumSeminorm p x = ∑ i ∈ s, p i (x i) := by sorry

end RiemannMasullo
