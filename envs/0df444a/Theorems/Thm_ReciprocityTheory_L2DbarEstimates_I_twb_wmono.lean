-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_twb_wmono
-- name    : ReciprocityTheory.L2DbarEstimates.I.twb_wmono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:04.258961+00:00
-- url     : https://prove2.me/theorems/3366c4f5-a62b-5606-842f-57231d3b9bca
-- title:
--   I: twb wmono
-- statement:
--   The I construction uses the twb wmono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean#L98-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwBound.lean#L98-L106

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

theorem ReciprocityTheory.L2DbarEstimates.I.twb_wmono {α : Type*} [MeasurableSpace α] (μ : Measure α) (f ρ₁ ρ₂ : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ x, 0 ≤ f x) (h : ∀ x, ρ₁ x ≤ c * ρ₂ x) :
    ∫⁻ x, ENNReal.ofReal (f x * ρ₁ x) ∂μ ≤ ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x * ρ₂ x) ∂μ := by sorry
