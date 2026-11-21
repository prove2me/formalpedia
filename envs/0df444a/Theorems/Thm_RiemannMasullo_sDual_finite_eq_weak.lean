-- Prove2me | Theorems.Thm_RiemannMasullo_sDual_finite_eq_weak
-- name    : RiemannMasullo.sDual_finite_eq_weak
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:18.499031+00:00
-- url     : https://prove2.me/theorems/371ebf96-5905-465c-8e05-1fc4b21c1ed9
-- title:
--   Finite-set convergence on the dual
-- statement:
--   Uniform convergence on finite subsets gives the weak topology on the continuous complex dual.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L128-L132

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

theorem sDual_finite_eq_weak :
    (inferInstance : TopologicalSpace (SDual E {T | T.Finite})) =
      (inferInstance : TopologicalSpace (WeakDual ℂ E)) := by sorry

end RiemannMasullo
