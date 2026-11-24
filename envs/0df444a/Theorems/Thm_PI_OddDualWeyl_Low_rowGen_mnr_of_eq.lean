-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_of_eq
-- name    : PI.OddDualWeyl.Low.rowGen_mnr_of_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:48.81483+00:00
-- url     : https://prove2.me/theorems/774c34c5-4e55-4911-aadf-918981fef6a3
-- title:
--   Low: row Gen mnr of eq
-- statement:
--   The Low construction uses the row Gen mnr of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L51-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L51-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.Low.rowGen_mnr_of_eq {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hρ : Function.Injective ρ) (p0 : Fin n) (hp0 : ρ p0 = b) :
    rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) +
      Polynomial.X * Polynomial.C (mnr R h (Function.update ρ p0 a)) := by sorry
