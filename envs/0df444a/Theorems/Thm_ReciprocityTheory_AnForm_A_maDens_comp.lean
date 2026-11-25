-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp
-- name    : ReciprocityTheory.AnForm.A.maDens_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:48.354334+00:00
-- url     : https://prove2.me/theorems/b99e1f27-2a1d-441e-b441-78e1d3c9e67b
-- title:
--   A: ma Dens comp
-- statement:
--   The A construction uses the ma Dens comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L51-L59

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Matrix
noncomputable section
variable {D E : ℕ}

theorem ReciprocityTheory.AnForm.A.maDens_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z)) :
    maDens (fun k => φ k ∘ τ) z = maDens φ (τ z) * Complex.normSq (jacC τ z).det := by sorry
