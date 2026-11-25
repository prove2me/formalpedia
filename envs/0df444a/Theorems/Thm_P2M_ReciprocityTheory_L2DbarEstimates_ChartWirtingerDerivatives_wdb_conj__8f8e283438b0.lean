-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_conj__8f8e283438b0
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_conj__8f8e283438b0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:30.083795+00:00
-- url     : https://prove2.me/theorems/7d9f2cdb-366c-4500-9f5d-ff338185c74d
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb conj  8f8e283438b0: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb conj  8f8e283438b0
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb conj  8f8e283438b0 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb conj  8f8e283438b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L97-L100

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_conj__8f8e283438b0 (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wdb n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wd n j g y) := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wdb_conj'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_conj__8f8e283438b0
