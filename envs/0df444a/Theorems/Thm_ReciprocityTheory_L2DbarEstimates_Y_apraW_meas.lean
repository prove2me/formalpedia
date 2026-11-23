-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_apraW_meas
-- name    : ReciprocityTheory.L2DbarEstimates.Y.apraW_meas
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:38.653261+00:00
-- url     : https://prove2.me/theorems/34d6d470-f610-4554-850b-082477d67fc3
-- title:
--   Y: apra W meas
-- statement:
--   The Y construction uses the apra W meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean#L13-L17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.apraW_meas (d : ℕ) (ε τ : ℝ) : Measurable (apraW d ε τ) := by sorry
