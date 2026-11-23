-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_holo
-- name    : ReciprocityTheory.L2DbarEstimates.Y.dbv_holo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:08.291081+00:00
-- url     : https://prove2.me/theorems/9020daa6-6192-4b9e-ac17-8981101a0190
-- title:
--   Y: dbv holo
-- statement:
--   The Y construction uses the dbv holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxE.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxE.lean#L18-L23

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

theorem ReciprocityTheory.L2DbarEstimates.Y.dbv_holo {n : ℕ} {G : V n → ℂ} {v : V n} (hG : DifferentiableAt ℂ G v) (ζ : V n) :
    dbv (fderiv ℝ G v) ζ = 0 := by sorry
