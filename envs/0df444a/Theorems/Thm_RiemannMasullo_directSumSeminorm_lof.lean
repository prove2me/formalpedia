-- Prove2me | Theorems.Thm_RiemannMasullo_directSumSeminorm_lof
-- name    : RiemannMasullo.directSumSeminorm_lof
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:25:59.773938+00:00
-- url     : https://prove2.me/theorems/4c444022-c647-40c7-bff5-f915907bc619
-- title:
--   Restriction of a direct-sum seminorm to one summand
-- statement:
--   On a vector included from a single summand, the direct-sum seminorm equals that summand’s given seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/Analysis/Normed/Module/Seminorm/DirectSum.lean#L35-L37

import Definitions.Def_RiemannMasullo_DirectSumSeminorm

open scoped DirectSum
open RiemannMasullo
variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

namespace RiemannMasullo

theorem directSumSeminorm_lof (p : ∀ i, Seminorm 𝕜 (X i)) (i : ι) (x : X i) :
    directSumSeminorm p (DirectSum.lof 𝕜 ι X i x) = p i x := by sorry

end RiemannMasullo
