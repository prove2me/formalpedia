-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_comp_real__8a691ef8d1ef
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_comp_real__8a691ef8d1ef
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:04.662854+00:00
-- url     : https://prove2.me/theorems/88bb31e8-c7c9-4efe-b6d7-982884cbd943
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd comp real  8a691ef8d1ef: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd comp real  8a691ef8d1ef
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd comp real  8a691ef8d1ef construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd comp real  8a691ef8d1ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L107-L121

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_comp_real__8a691ef8d1ef (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (p : V n → ℝ) (y : V n)
    (hk : DifferentiableAt ℝ k (p y)) (hp : DifferentiableAt ℝ p y) :
    wd n j (fun w => ((k (p w) : ℝ) : ℂ)) y = ((deriv k (p y) : ℝ) : ℂ) * wd n j (fun w => (p w : ℂ)) y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wd_comp_real'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_comp_real__8a691ef8d1ef
