-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmPrim_hasDerivAt
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rmPrim_hasDerivAt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:31.33574+00:00
-- url     : https://prove2.me/theorems/a5088f6d-a995-46c9-bccc-55bf6cc10b9c
-- title:
--   Y: rm Prim has Deriv At
-- statement:
--   The Y construction uses the rm Prim has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L44-L45

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

theorem ReciprocityTheory.L2DbarEstimates.Y.rmPrim_hasDerivAt (t : ℝ) : HasDerivAt rmPrim (rmStep t) t := by sorry
