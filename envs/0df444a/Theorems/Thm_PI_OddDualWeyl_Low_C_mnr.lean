-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_C_mnr
-- name    : PI.OddDualWeyl.Low.C_mnr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:52.023476+00:00
-- url     : https://prove2.me/theorems/79cc58bb-c25a-444b-a861-d21e62727531
-- title:
--   Low: C mnr
-- statement:
--   The Low construction uses the C mnr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L37-L42

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

theorem PI.OddDualWeyl.Low.C_mnr {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) :
    (Polynomial.C (mnr R h ρ) : Polynomial (MvPolynomial (Fin k × Fin k) R)) =
      (Matrix.of fun p q : Fin n =>
        Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R)).det := by sorry
