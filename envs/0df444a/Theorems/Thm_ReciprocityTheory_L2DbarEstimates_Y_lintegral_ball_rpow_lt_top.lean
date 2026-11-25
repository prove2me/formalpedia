-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_lintegral_ball_rpow_lt_top
-- name    : ReciprocityTheory.L2DbarEstimates.Y.lintegral_ball_rpow_lt_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:12.01731+00:00
-- url     : https://prove2.me/theorems/6a1961f4-38ca-48a6-bf83-608b21ac7ee6
-- title:
--   Y: lintegral ball rpow lt top
-- statement:
--   The Y construction uses the lintegral ball rpow lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L168-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/LintegralBallRpowLtTop.lean#L168-L190

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.lintegral_ball_rpow_lt_top {n : ℕ} (hMVI : MVIntStatement n) (hn : 1 ≤ n) (vP : V n)
    {r : ℝ} (hr : r ≤ 1) {a : ℝ} (ha : a < n) :
    ∫⁻ v in Metric.ball vP r, ENNReal.ofReal ‖v - vP‖ ^ (-2 * a) < ⊤ := by sorry
