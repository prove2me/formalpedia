-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_wdb_eq
-- name    : ReciprocityTheory.L2DbarEstimates.Y.sum_wdb_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:23.816193+00:00
-- url     : https://prove2.me/theorems/e386739b-ae4b-4b46-abaa-10ed1ff8c769
-- title:
--   Y: sum wdb eq
-- statement:
--   The Y construction uses the sum wdb eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L36-L43

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Y.sum_wdb_eq {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wdb n k g y * conj (ζ k) = dbv (fderiv ℝ g y) ζ := by sorry
