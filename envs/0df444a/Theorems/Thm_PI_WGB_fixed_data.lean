-- Prove2me | Theorems.Thm_PI_WGB_fixed_data
-- name    : PI.WGB.fixed_data
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:59.216712+00:00
-- url     : https://prove2.me/theorems/2917ab2f-5e65-433e-8f72-7400f125c0b4
-- title:
--   WGB: fixed data
-- statement:
--   The WGB construction uses the fixed data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L89-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/TransposeConjComm.lean#L89-L113

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem PI.WGB.fixed_data {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ) (c : ℤ) (w : Fin n → ℤ)
    (κ : Fin n → ℕ) (hwκ : ∀ i, (κ i : ℤ) + c = w i)
    (hU0 : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) →
      (∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) →
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ c) • rowAct ℂ (iotaC ℂ n k g).transpose f = f)
    (hT0 : ∀ t : Fin n → ℂˣ, ((∏ i, (t i : ℂ)) ^ c) •
      rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f = (∏ i, (t i : ℂ) ^ w i) • f) :
    (∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f) ∧
    (∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f) := by sorry
