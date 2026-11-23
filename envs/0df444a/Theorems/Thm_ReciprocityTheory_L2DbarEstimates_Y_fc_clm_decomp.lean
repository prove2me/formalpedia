-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_clm_decomp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fc_clm_decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:41.948929+00:00
-- url     : https://prove2.me/theorems/7ee7857e-9bcb-480e-9f1a-c3834ce4769e
-- title:
--   Y: fc clm decomp
-- statement:
--   The Y construction uses the fc clm decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcA.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcA.lean#L10-L26

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalcA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.fc_clm_decomp (n : ℕ) (D : V n →L[ℝ] ℂ) (u : V n) :
    D u = ∑ a, ((D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * u a +
      (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (u a)) := by sorry
