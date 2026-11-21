-- Prove2me | Theorems.Thm_RiemannMasullo_mappingSeminorm_apply
-- name    : RiemannMasullo.mappingSeminorm_apply
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:25.09901+00:00
-- url     : https://prove2.me/theorems/79e3dda6-50f3-4ce2-93a3-59200253e9e2
-- title:
--   Evaluation of the mapping seminorm
-- statement:
--   For a continuous linear map, the mapping seminorm associated with a bounded test set and a continuous target seminorm equals the supremum of the pointwise seminorm values.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L98-L108

import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

namespace RiemannMasullo

theorem mappingSeminorm_apply (T : {T : Set E // IsVonNBounded ℂ T})
    (p : {p : Seminorm ℂ F // Continuous p}) (f : E →L[ℂ] F) :
    mappingSeminorm T p f = ⨆ x : T.val, p.val (f x) := by sorry

end RiemannMasullo
