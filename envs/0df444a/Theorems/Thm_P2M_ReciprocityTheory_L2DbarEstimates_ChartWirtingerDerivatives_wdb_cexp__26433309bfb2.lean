-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_cexp__26433309bfb2
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_cexp__26433309bfb2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:46.110339+00:00
-- url     : https://prove2.me/theorems/3f0b617e-c40a-53f7-b0b2-8e8ed3233772
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb cexp  26433309bfb2: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb cexp  26433309bfb2
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb cexp  26433309bfb2 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb cexp  26433309bfb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L84-L87

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_cexp__26433309bfb2 (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y) :
    wdb n j (fun w => Complex.exp (g w)) y = Complex.exp (g y) * wdb n j g y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wdb_cexp'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_cexp__26433309bfb2
