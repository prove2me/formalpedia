-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_four_bound
-- name    : ReciprocityTheory.L2DbarEstimates.Y.four_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:29.401833+00:00
-- url     : https://prove2.me/theorems/4f2871db-0259-4182-821e-2cd28e4edce9
-- title:
--   Y: four bound
-- statement:
--   The Y construction uses the four bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourBasic.lean#L36-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourBasic.lean#L36-L62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic
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
universe u

theorem ReciprocityTheory.L2DbarEstimates.Y.four_bound (f : ℕ) : FOURBoundStatement f := by sorry
