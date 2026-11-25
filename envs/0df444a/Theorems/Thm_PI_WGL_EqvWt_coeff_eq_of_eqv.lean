-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_coeff_eq_of_eqv
-- name    : PI.WGL.EqvWt.coeff_eq_of_eqv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:32.250803+00:00
-- url     : https://prove2.me/theorems/f6edf789-2f38-4461-98b5-82ae9645f91b
-- title:
--   Eqv Wt: coeff eq of eqv
-- statement:
--   The Eqv Wt construction uses the coeff eq of eqv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L141-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L141-L153

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

theorem PI.WGL.EqvWt.coeff_eq_of_eqv {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (t : Fin n → ℂˣ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (κ : ℂ) (hκ : sqAct ℂ n mu (diagGL ℂ n t) s = κ • s) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : coeff m (φ s) ≠ 0) :
    (∏ i, (t i : ℂ)) ^ lam.detShift * ∏ i, (t i : ℂ) ^ rowDeg m (Fin.castSucc i) = κ := by sorry
