-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_smul
-- name    : ReciprocityTheory.L2DbarEstimates.Y.dbv_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:59.181864+00:00
-- url     : https://prove2.me/theorems/7ef64549-59bd-4648-a338-3526a0226ccf
-- title:
--   Y: dbv smul
-- statement:
--   The Y construction uses the dbv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxE.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxE.lean#L14-L16

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.dbv_smul {n : ℕ} (c : ℂ) (D : V n →L[ℝ] ℂ) (ζ : V n) : dbv (c • D) ζ = c * dbv D ζ := by sorry
