-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_cHess_comp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:57.266+00:00
-- url     : https://prove2.me/theorems/e01a3a73-1d80-58b9-b503-a5584c814adf
-- title:
--   Y: cmpa c Hess comp
-- statement:
--   The Y construction uses the cmpa c Hess comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaCHessComp.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaCHessComp.lean#L16-L26

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) :
    cHess n (h ∘ τ) x = (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).transpose * cHess n h (τ x) *
      (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj := by sorry
