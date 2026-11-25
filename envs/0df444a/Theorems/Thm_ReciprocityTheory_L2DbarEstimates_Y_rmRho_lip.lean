-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_lip
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rmRho_lip
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:59.942657+00:00
-- url     : https://prove2.me/theorems/21b0a5d4-829c-5ba7-a989-e2c69fc9340b
-- title:
--   Y: rm Rho lip
-- statement:
--   The Y construction uses the rm Rho lip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L122-L128

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

theorem ReciprocityTheory.L2DbarEstimates.Y.rmRho_lip (a b : ℝ) : |rmRho a - rmRho b| ≤ |a - b| := by sorry
