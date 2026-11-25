-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmStep_monotone
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rmStep_monotone
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:08.153814+00:00
-- url     : https://prove2.me/theorems/1d799a70-7f6d-4811-833f-75e7aa1c8c93
-- title:
--   Y: rm Step monotone
-- statement:
--   The Y construction uses the rm Step monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L19-L23

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

theorem ReciprocityTheory.L2DbarEstimates.Y.rmStep_monotone : Monotone rmStep := by sorry
