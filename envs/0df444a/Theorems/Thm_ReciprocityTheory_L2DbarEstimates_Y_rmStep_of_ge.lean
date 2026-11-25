-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmStep_of_ge
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rmStep_of_ge
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:25.731143+00:00
-- url     : https://prove2.me/theorems/0ed95b17-3e83-5b50-bd7c-50858de32ce3
-- title:
--   Y: rm Step of ge
-- statement:
--   The Y construction uses the rm Step of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L30-L33

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

theorem ReciprocityTheory.L2DbarEstimates.Y.rmStep_of_ge (t : ℝ) (h : t ≤ -1 / 2) : rmStep t = -1 := by sorry
