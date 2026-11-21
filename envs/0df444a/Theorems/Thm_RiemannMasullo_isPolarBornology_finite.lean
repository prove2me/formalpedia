-- Prove2me | Theorems.Thm_RiemannMasullo_isPolarBornology_finite
-- name    : RiemannMasullo.isPolarBornology_finite
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:34:13.672606+00:00
-- url     : https://prove2.me/theorems/f68b3265-5e67-4bfd-ac7c-498647041bb4
-- title:
--   Finite sets form a polar bornology
-- statement:
--   The finite subsets form a polar bornology in the sense of Appendix C.2.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L268-L273

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

theorem isPolarBornology_finite : IsPolarBornology {T : Set E | T.Finite} := by sorry

end RiemannMasullo
