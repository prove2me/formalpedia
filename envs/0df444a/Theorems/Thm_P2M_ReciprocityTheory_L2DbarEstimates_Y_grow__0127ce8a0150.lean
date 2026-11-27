-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_grow__0127ce8a0150
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_grow__0127ce8a0150
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:23.825928+00:00
-- url     : https://prove2.me/theorems/6d3610b4-08d4-4232-8f3d-8b661f31b229
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y grow  0127ce8a0150: P2 M Reciprocity Theory L2 Dbar Estimates Y grow  0127ce8a0150
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y grow  0127ce8a0150 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y grow  0127ce8a0150 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/GrowSumIndicatorLe.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/GrowSumIndicatorLe.lean#L12-L36

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GrowSumIndicatorLe
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

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_grow__0127ce8a0150.{u1, u2} (hC : GROWCountStatement.{u1, u2}) : GROWStatement.{u1, u2} := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«grow».«» := P2M_ReciprocityTheory_L2DbarEstimates_Y_grow__0127ce8a0150
