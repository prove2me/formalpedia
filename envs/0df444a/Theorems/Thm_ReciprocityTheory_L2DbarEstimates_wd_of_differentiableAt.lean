-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
-- name    : ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:44.798007+00:00
-- url     : https://prove2.me/theorems/d3234333-0f2c-4365-a167-05f0b62531cb
-- title:
--   L2 Dbar Estimates: wd of differentiable At
-- statement:
--   The L2 Dbar Estimates construction uses the wd of differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L158-L162

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

theorem ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wd n j f x = fderiv ℂ f x (bas n j) := by sorry
