-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_jacC_eq_toMatrix__103ab3916728
-- name    : P2M_ReciprocityTheory_AnForm_A_jacC_eq_toMatrix__103ab3916728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:44.455389+00:00
-- url     : https://prove2.me/theorems/2a452395-927f-436b-820b-924c5a216443
-- title:
--   P2 M Reciprocity Theory An Form A jac C eq to Matrix  103ab3916728: P2 M Reciprocity Theory An Form A jac C eq to Matrix  103ab3916728
-- statement:
--   The P2 M Reciprocity Theory An Form A jac C eq to Matrix  103ab3916728 construction uses the P2 M Reciprocity Theory An Form A jac C eq to Matrix  103ab3916728 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LintegralImageEqLintegralNormSqDetMul.lean#L22-L26

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

theorem P2M_ReciprocityTheory_AnForm_A_jacC_eq_toMatrix__103ab3916728 (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) :
    jacC τ z = LinearMap.toMatrix' (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin E → ℂ)) := by sorry

alias «ReciprocityTheory».«AnForm».«A».«jacC_eq_toMatrix'» := P2M_ReciprocityTheory_AnForm_A_jacC_eq_toMatrix__103ab3916728
