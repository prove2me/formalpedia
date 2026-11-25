-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_twb_sub_le
-- name    : ReciprocityTheory.L2DbarEstimates.I.twb_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:28.475941+00:00
-- url     : https://prove2.me/theorems/a0ea9e57-cbf3-45ca-af4b-65435a1eb3fc
-- title:
--   I: twb sub le
-- statement:
--   The I construction uses the twb sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean#L65-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean#L65-L96

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.twb_sub_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℂ) (ρ : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x) :
    ∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x) ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) ∂μ := by sorry
