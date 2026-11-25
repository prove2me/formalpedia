-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_abs_rmStep_le
-- name    : ReciprocityTheory.L2DbarEstimates.Y.abs_rmStep_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:19.293828+00:00
-- url     : https://prove2.me/theorems/dc8f9a40-8ea7-4c38-909a-b4d171e4c946
-- title:
--   Y: abs rm Step le
-- statement:
--   The Y construction uses the abs rm Step le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L35-L40

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.abs_rmStep_le (t : ℝ) : |rmStep t| ≤ 1 := by sorry
