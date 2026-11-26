-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_add__2b03dcc92c3f
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_add__2b03dcc92c3f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:31.017014+00:00
-- url     : https://prove2.me/theorems/54e26bc0-f2e0-5206-885c-e9fa2db15d8e
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd add  2b03dcc92c3f: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd add  2b03dcc92c3f
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd add  2b03dcc92c3f construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wd add  2b03dcc92c3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L45-L48

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_add__2b03dcc92c3f (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) : wd n j (fun w => g w + h w) y = wd n j g y + wd n j h y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wd_add'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_add__2b03dcc92c3f
