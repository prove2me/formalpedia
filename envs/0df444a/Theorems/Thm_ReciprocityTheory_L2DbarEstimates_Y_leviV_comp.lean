-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_leviV_comp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.leviV_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:00:07.455186+00:00
-- url     : https://prove2.me/theorems/9c5d18e7-a4e0-4031-b8b7-ed014dc57ac9
-- title:
--   Y: levi V comp
-- statement:
--   The Y construction uses the levi V comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L157-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean#L157-L212

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

theorem ReciprocityTheory.L2DbarEstimates.Y.leviV_comp {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {y : V n}
    (hf : ContDiffAt ℝ 2 f (Φ y)) (hΦ : ContDiffAt ℂ 2 Φ y) (ξ : Fin n → ℂ) :
    leviV n (f ∘ Φ) y ξ = leviV n f (Φ y) (fderiv ℂ Φ y (WithLp.toLp 2 ξ)).ofLp := by sorry
