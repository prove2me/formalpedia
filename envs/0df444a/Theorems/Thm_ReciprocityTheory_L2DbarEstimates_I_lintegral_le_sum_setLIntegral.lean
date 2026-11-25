-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_lintegral_le_sum_setLIntegral
-- name    : ReciprocityTheory.L2DbarEstimates.I.lintegral_le_sum_setLIntegral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:21.635992+00:00
-- url     : https://prove2.me/theorems/354d4459-0770-5af8-890b-17cebee974e7
-- title:
--   I: lintegral le sum set LIntegral
-- statement:
--   The I construction uses the lintegral le sum set LIntegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L69-L81

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.lintegral_le_sum_setLIntegral {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (U : ι → Set α) (hU : ∀ i ∈ s, MeasurableSet (U i)) (f : α → ℝ≥0∞) (h : ι → α → ℝ≥0∞)
    (hsupp : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ U i) (hle : ∀ i ∈ s, ∀ x ∈ U i, f x ≤ h i x) :
    ∫⁻ x, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ := by sorry
