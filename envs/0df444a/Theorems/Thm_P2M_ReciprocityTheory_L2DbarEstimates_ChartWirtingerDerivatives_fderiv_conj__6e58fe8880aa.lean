-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_fderiv_conj__6e58fe8880aa
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_fderiv_conj__6e58fe8880aa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:42.031937+00:00
-- url     : https://prove2.me/theorems/c442d404-5ffe-4737-8ef1-392266984d97
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives fderiv conj  6e58fe8880aa: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives fderiv conj  6e58fe8880aa
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives fderiv conj  6e58fe8880aa construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives fderiv conj  6e58fe8880aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L89-L95

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_fderiv_conj__6e58fe8880aa (n : ℕ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (starRingEnd ℂ) (g w)) y v = (starRingEnd ℂ) (fderiv ℝ g y v) := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«fderiv_conj'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_fderiv_conj__6e58fe8880aa
