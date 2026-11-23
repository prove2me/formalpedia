-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_real_of_complex
-- name    : ReciprocityTheory.L2DbarEstimates.fderiv_real_of_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:30.815249+00:00
-- url     : https://prove2.me/theorems/6d5c3d6c-a183-4138-8796-832e704d9e4d
-- title:
--   L2 Dbar Estimates: fderiv real of complex
-- statement:
--   The L2 Dbar Estimates construction uses the fderiv real of complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L147-L150

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.fderiv_real_of_complex {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℂ f x) (w : V n) :
    fderiv ℝ f x w = fderiv ℂ f x w := by sorry
