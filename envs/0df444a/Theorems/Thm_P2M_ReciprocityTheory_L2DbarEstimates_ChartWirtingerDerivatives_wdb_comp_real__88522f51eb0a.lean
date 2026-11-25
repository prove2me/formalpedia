-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_comp_real__88522f51eb0a
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_comp_real__88522f51eb0a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:41.129852+00:00
-- url     : https://prove2.me/theorems/cfac5a9a-99f1-50d1-9b82-1b03e3a527e2
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb comp real  88522f51eb0a: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb comp real  88522f51eb0a
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb comp real  88522f51eb0a construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb comp real  88522f51eb0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L123-L137

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_comp_real__88522f51eb0a (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (p : V n → ℝ) (y : V n)
    (hk : DifferentiableAt ℝ k (p y)) (hp : DifferentiableAt ℝ p y) :
    wdb n j (fun w => ((k (p w) : ℝ) : ℂ)) y = ((deriv k (p y) : ℝ) : ℂ) * wdb n j (fun w => (p w : ℂ)) y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wdb_comp_real'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_comp_real__88522f51eb0a
