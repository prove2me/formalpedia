-- Prove2me | Theorems.Thm_RiemannMasullo_polarSeminorm_closedUnitBall
-- name    : RiemannMasullo.polarSeminorm_closedUnitBall
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:06.583369+00:00
-- url     : https://prove2.me/theorems/89d73aae-e788-48cd-ae9b-4a7c3ceb19ed
-- title:
--   The unit ball of a polar seminorm
-- statement:
--   For a complex bilinear pairing and a weakly bounded test set in its second variable, the closed unit ball of the polar seminorm is the absolute polar of the test set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L334-L347

import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

open scoped ComplexOrder
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)

namespace RiemannMasullo

theorem polarSeminorm_closedUnitBall
    (A : {A : Set F // IsVonNBounded (E := WeakBilin B.flip) ℂ A}) :
    (polarSeminorm B A).closedBall 0 1 = B.flip.polar A.val := by sorry

end RiemannMasullo
