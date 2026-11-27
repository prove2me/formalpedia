-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_norm_dbv_le
-- name    : ReciprocityTheory.L2DbarEstimates.Y.norm_dbv_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:07.888261+00:00
-- url     : https://prove2.me/theorems/ccc18b30-297e-4155-82ca-c6a4ac1ebc6e
-- title:
--   Y: norm dbv le
-- statement:
--   The Y construction uses the norm dbv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L54-L64

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

theorem ReciprocityTheory.L2DbarEstimates.Y.norm_dbv_le {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ‖dbv D ζ‖ ≤ ‖D‖ * ‖ζ‖ := by sorry
