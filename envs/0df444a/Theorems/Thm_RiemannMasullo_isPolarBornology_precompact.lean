-- Prove2me | Theorems.Thm_RiemannMasullo_isPolarBornology_precompact
-- name    : RiemannMasullo.isPolarBornology_precompact
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:27.270836+00:00
-- url     : https://prove2.me/theorems/759dd6fe-c74c-4d23-8739-27b204b2220a
-- title:
--   Precompact sets form a polar bornology
-- statement:
--   The sets with compact closure in the completion form a polar bornology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L276-L291

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

theorem isPolarBornology_precompact :
    IsPolarBornology {T : Set E | IsPrecompactInCompletion T} := by sorry

end RiemannMasullo
