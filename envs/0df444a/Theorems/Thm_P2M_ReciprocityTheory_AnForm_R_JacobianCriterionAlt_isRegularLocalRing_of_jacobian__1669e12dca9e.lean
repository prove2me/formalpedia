-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isRegularLocalRing_of_jacobian__1669e12dca9e
-- name    : P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isRegularLocalRing_of_jacobian__1669e12dca9e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:13.855105+00:00
-- url     : https://prove2.me/theorems/b18eeefb-90a7-410a-9777-7db9e7330b22
-- title:
--   P2 M Reciprocity Theory An Form R Jacobian Criterion Alt is Regular Local Ring of jacobian  1669e12dca9e: P2 M Reciprocity Theory An Form R Jacobian Criterion Alt is Regular Local Ring of jacobian  16
-- statement:
--   The P2 M Reciprocity Theory An Form R Jacobian Criterion Alt is Regular Local Ring of jacobian  1669e12dca9e construction uses the P2 M Reciprocity Theory An Form R Jacobian Criterion Alt is Regular Local Ring of jacobian  1669e12dca9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartC.lean#L12-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartC.lean#L12-L89

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}

theorem P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isRegularLocalRing_of_jacobian__1669e12dca9e (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => gradP p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptI p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locR K p) ∧ ringKrullDim (locR K p) = ((n - c : ℕ) : WithBot ℕ∞) := by sorry

alias «ReciprocityTheory».«AnForm».«R».«JacobianCriterionAlt».«isRegularLocalRing_of_jacobian'» := P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isRegularLocalRing_of_jacobian__1669e12dca9e
