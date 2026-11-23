-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_ofReal
-- name    : ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:49:01.88781+00:00
-- url     : https://prove2.me/theorems/f01fa94d-8376-42be-81af-608a819acf83
-- title:
--   L2 Dbar Estimates: differentiable At of Real
-- statement:
--   The L2 Dbar Estimates construction uses the differentiable At of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L89-L91

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

theorem ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => (v y : ℂ)) x := by sorry
