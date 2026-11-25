-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fc_wdb_holo
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fc_wdb_holo
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:00:56.127802+00:00
-- url     : https://prove2.me/theorems/d76564f9-b015-4206-9ae0-5f7a8594e1c1
-- title:
--   Y: fc wdb holo
-- statement:
--   The Y construction uses the fc wdb holo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcA.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatCalcA.lean#L28-L33

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fc_wdb_holo (n : ℕ) (p : V n → ℂ) (v : V n) (hp : DifferentiableAt ℂ p v) (j : Fin n) :
    wdb n j p v = 0 := by sorry
