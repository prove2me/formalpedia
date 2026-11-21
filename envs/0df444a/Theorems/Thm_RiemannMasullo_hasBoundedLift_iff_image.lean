-- Prove2me | Theorems.Thm_RiemannMasullo_hasBoundedLift_iff_image
-- name    : RiemannMasullo.hasBoundedLift_iff_image
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:30:28.269795+00:00
-- url     : https://prove2.me/theorems/d91598c2-de16-4f49-b489-07c4c2b514e7
-- title:
--   Bounded lifts with prescribed image
-- statement:
--   For a continuous complex linear map, a target set contained in the image of a bounded set is itself the image of a bounded set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L709-L716

import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
open RiemannMasullo
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

namespace RiemannMasullo

theorem hasBoundedLift_iff_image (f : E →L[ℂ] F) (B : Set F) :
    HasBoundedLift f B ↔ ∃ A : Set E, IsVonNBounded ℂ A ∧ f '' A = B := by sorry

end RiemannMasullo
