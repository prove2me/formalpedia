-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_cmpa_hess_comp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:16.762833+00:00
-- url     : https://prove2.me/theorems/2107454a-901e-491f-a94d-09ae9a3027ce
-- title:
--   Y: cmpa hess comp
-- statement:
--   The Y construction uses the cmpa hess comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaFderivCompApply.lean#L116-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/CmpaFderivCompApply.lean#L116-L150

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaFderivCompApply
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

theorem ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) (j k : Fin n) :
    wd n j (wdb n k (h ∘ τ)) x = ∑ m, ∑ l, wd n l (wdb n m h) (τ x) *
      (fderiv ℂ τ x (bas n j)) l * conj ((fderiv ℂ τ x (bas n k)) m) := by sorry
