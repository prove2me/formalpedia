-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_const_mul__4f4e797ecfdd
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_const_mul__4f4e797ecfdd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:40.743351+00:00
-- url     : https://prove2.me/theorems/54f016e7-d15a-5f29-92a2-a9b10088a4d8
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd const mul  4f4e797ecfdd: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd const mul  4f4e797ecfdd
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd const mul  4f4e797ecfdd construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd const mul  4f4e797ecfdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L55-L58

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_const_mul__4f4e797ecfdd (n : ℕ) (j : Fin n) (c : ℂ) (g : V n → ℂ) (y : V n)
    (hg : DifferentiableAt ℝ g y) : wd n j (fun w => c * g w) y = c * wd n j g y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wd_const_mul'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_const_mul__4f4e797ecfdd
