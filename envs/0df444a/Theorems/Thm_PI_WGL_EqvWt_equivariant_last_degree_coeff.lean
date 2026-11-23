-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_equivariant_last_degree_coeff
-- name    : PI.WGL.EqvWt.equivariant_last_degree_coeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:25.910892+00:00
-- url     : https://prove2.me/theorems/3472a29a-b03e-4021-820b-c4e88ade0a19
-- title:
--   Eqv Wt: equivariant last degree coeff
-- statement:
--   The Eqv Wt construction uses the equivariant last degree coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L155-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L155-L189

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt

theorem PI.WGL.EqvWt.equivariant_last_degree_coeff {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : coeff m (φ s) ≠ 0) :
    ((rowDeg m (Fin.last n) : ℕ) : ℤ) = wsum lam - wsum mu - lam.detShift := by sorry
