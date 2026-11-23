-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_deriv_of_contDiffAt
-- name    : ReciprocityTheory.L2DbarEstimates.differentiableAt_deriv_of_contDiffAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:15.543065+00:00
-- url     : https://prove2.me/theorems/85670cbf-20ab-4edb-84e7-a43a617cf71e
-- title:
--   L2 Dbar Estimates: differentiable At deriv of cont Diff At
-- statement:
--   The L2 Dbar Estimates construction uses the differentiable At deriv of cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EventuallyDifferentiableAtOfContDiffAt.lean#L186-L191

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

theorem ReciprocityTheory.L2DbarEstimates.differentiableAt_deriv_of_contDiffAt {k : ℝ → ℝ} {t : ℝ} (hk : ContDiffAt ℝ 2 k t) :
    DifferentiableAt ℝ (deriv k) t := by sorry
