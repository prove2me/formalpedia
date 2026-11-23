-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
-- name    : ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:28.945156+00:00
-- url     : https://prove2.me/theorems/4658bc5e-acf0-4293-a1d1-78a872ca1427
-- title:
--   A: integrable On image iff analytic
-- statement:
--   The A construction uses the integrable On image iff analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L120-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L120-L134

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

theorem ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    IntegrableOn f (τ '' U) ↔
      IntegrableOn (fun z => Complex.normSq (jacC τ z).det • f (τ z)) U := by sorry
