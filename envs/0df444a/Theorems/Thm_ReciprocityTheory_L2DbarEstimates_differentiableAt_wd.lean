-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wd
-- name    : ReciprocityTheory.L2DbarEstimates.differentiableAt_wd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:25.585926+00:00
-- url     : https://prove2.me/theorems/36e49e96-392b-41b9-8d9b-b1e47999109a
-- title:
--   L2 Dbar Estimates: differentiable At wd
-- statement:
--   The L2 Dbar Estimates construction uses the differentiable At wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L175-L184

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

theorem ReciprocityTheory.L2DbarEstimates.differentiableAt_wd {j : Fin n} {f : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (wd n j f) x := by sorry
