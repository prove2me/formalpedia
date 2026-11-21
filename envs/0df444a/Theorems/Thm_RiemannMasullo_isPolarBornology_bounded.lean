-- Prove2me | Theorems.Thm_RiemannMasullo_isPolarBornology_bounded
-- name    : RiemannMasullo.isPolarBornology_bounded
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:14.126115+00:00
-- url     : https://prove2.me/theorems/11485d8a-1442-4dac-bea9-775b69b73d14
-- title:
--   Bounded sets form a polar bornology
-- statement:
--   The von Neumann bounded sets form a polar bornology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L294-L300

import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [PolynormableSpace ℂ E] [T2Space E]

namespace RiemannMasullo

theorem isPolarBornology_bounded : IsPolarBornology {T : Set E | IsVonNBounded ℂ T} := by sorry

end RiemannMasullo
