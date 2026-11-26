-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_add__ce3b181f28a2
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_add__ce3b181f28a2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:55.146877+00:00
-- url     : https://prove2.me/theorems/47ddff05-e11c-4f3f-8440-985a622f845f
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb add  ce3b181f28a2: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb add  ce3b181f28a2
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb add  ce3b181f28a2 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb add  ce3b181f28a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L50-L53

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_add__ce3b181f28a2 (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) : wdb n j (fun w => g w + h w) y = wdb n j g y + wdb n j h y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wdb_add'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_add__ce3b181f28a2
