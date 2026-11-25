-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_cexp__5e52f4ad6c5d
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_cexp__5e52f4ad6c5d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:01.3772+00:00
-- url     : https://prove2.me/theorems/5df6c760-3213-43ad-a878-91d9ae7899bc
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd cexp  5e52f4ad6c5d: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd cexp  5e52f4ad6c5d
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd cexp  5e52f4ad6c5d construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd cexp  5e52f4ad6c5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L79-L82

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_cexp__5e52f4ad6c5d (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y) :
    wd n j (fun w => Complex.exp (g w)) y = Complex.exp (g y) * wd n j g y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wd_cexp'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_cexp__5e52f4ad6c5d
