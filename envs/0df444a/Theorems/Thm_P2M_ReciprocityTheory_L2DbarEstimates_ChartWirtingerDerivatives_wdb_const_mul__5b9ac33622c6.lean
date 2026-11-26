-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_const_mul__5b9ac33622c6
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_const_mul__5b9ac33622c6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:13.073815+00:00
-- url     : https://prove2.me/theorems/62a41aa3-44e3-448a-aec5-ee12148742dc
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb const mul  5b9ac33622c6: P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb const mul  5b9ac33622c6
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb const mul  5b9ac33622c6 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Chart Wirtinger Derivatives wdb const mul  5b9ac33622c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/DifferentiableAtChart.lean#L60-L63

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

theorem P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_const_mul__5b9ac33622c6 (n : ℕ) (j : Fin n) (c : ℂ) (g : V n → ℂ) (y : V n)
    (hg : DifferentiableAt ℝ g y) : wdb n j (fun w => c * g w) y = c * wdb n j g y := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«ChartWirtingerDerivatives».«wdb_const_mul'» := P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_const_mul__5b9ac33622c6
