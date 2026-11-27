-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_maInt_comp
-- name    : ReciprocityTheory.AnForm.A.maInt_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:01:24.59894+00:00
-- url     : https://prove2.me/theorems/1eb27e35-0050-4498-925b-4518944b77e3
-- title:
--   A: ma Int comp
-- statement:
--   The A construction uses the ma Int comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L136-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L136-L151

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

theorem ReciprocityTheory.AnForm.A.maInt_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ)
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U U' : Set (Fin D → ℂ)) (hU : IsOpen U) (hU' : IsOpen U')
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (himg : τ '' U = U')
    (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) U') :
    maInt (fun k => φ k ∘ τ) (g ∘ τ) U = maInt φ g U' := by sorry
