-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_jacobian_cut__05331927f463
-- name    : P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_jacobian_cut__05331927f463
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:56.994716+00:00
-- url     : https://prove2.me/theorems/bab5c705-1591-52dd-b8a0-010f827626e6
-- title:
--   P2 M Reciprocity Theory An Form R Jacobian Criterion Alt exists jacobian cut  05331927f463: P2 M Reciprocity Theory An Form R Jacobian Criterion Alt exists jacobian cut  05331927f463
-- statement:
--   The P2 M Reciprocity Theory An Form R Jacobian Criterion Alt exists jacobian cut  05331927f463 construction uses the P2 M Reciprocity Theory An Form R Jacobian Criterion Alt exists jacobian cut  05331927f463 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L168-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartB.lean#L168-L270

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
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

theorem P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_jacobian_cut__05331927f463 (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locR K p)] (he : ringKrullDim (locR K p) = e) :
    e ≤ n ∧ ∃ F : Fin (n - e) → MvPolynomial (Fin n) ℂ, (∀ i, F i ∈ K) ∧
      LinearIndependent ℂ (fun i => gradP p (F i)) ∧
      ∃ h : MvPolynomial (Fin n) ℂ, eval p h ≠ 0 ∧ ∀ g ∈ K, h * g ∈ Ideal.span (Set.range F) := by sorry

alias «ReciprocityTheory».«AnForm».«R».«JacobianCriterionAlt».«exists_jacobian_cut'» := P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_jacobian_cut__05331927f463
