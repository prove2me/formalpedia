-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_comp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.dbv_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:28.274231+00:00
-- url     : https://prove2.me/theorems/c17b3f3b-da10-4b91-9f78-7a312c0d124c
-- title:
--   Y: dbv comp
-- statement:
--   The Y construction uses the dbv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L101-L105

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

theorem ReciprocityTheory.L2DbarEstimates.Y.dbv_comp {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hf : DifferentiableAt ℝ f (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dbv (fderiv ℝ (f ∘ Φ) v) ζ = dbv (fderiv ℝ f (Φ v)) (fderiv ℂ Φ v ζ) := by sorry
