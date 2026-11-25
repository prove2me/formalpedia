-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_wd_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.sum_wd_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:01:05.900942+00:00
-- url     : https://prove2.me/theorems/5d1f5d4b-fd19-433d-93a7-ee1d76194f8b
-- title:
--   Y: sum wd eq
-- statement:
--   The Y construction uses the sum wd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L45-L52

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.sum_wd_eq {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wd n k g y * ζ k = dv (fderiv ℝ g y) ζ := by sorry
