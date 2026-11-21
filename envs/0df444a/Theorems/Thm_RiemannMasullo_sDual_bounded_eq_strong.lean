-- Prove2me | Theorems.Thm_RiemannMasullo_sDual_bounded_eq_strong
-- name    : RiemannMasullo.sDual_bounded_eq_strong
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:08.918283+00:00
-- url     : https://prove2.me/theorems/83f35f1f-e7e9-4e88-8ae9-bdef3e9bdb0f
-- title:
--   Bounded-set convergence on the dual
-- statement:
--   Uniform convergence on all von Neumann bounded subsets gives the strong topology on the continuous complex dual.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L136-L138

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

theorem sDual_bounded_eq_strong :
    (inferInstance : TopologicalSpace (SDual E {T | IsVonNBounded ℂ T})) =
      (inferInstance : TopologicalSpace (StrongDual ℂ E)) := by sorry

end RiemannMasullo
