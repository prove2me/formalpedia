-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_mat
-- name    : PI.OddDualWeyl.Low.rowGen_mnr_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:55.015946+00:00
-- url     : https://prove2.me/theorems/616216eb-a1f0-4f3c-b771-f1d891fa1373
-- title:
--   Low: row Gen mnr mat
-- statement:
--   The Low construction uses the row Gen mnr mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L28-L35

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

theorem PI.OddDualWeyl.Low.rowGen_mnr_mat {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k) :
    rowGen R a b (mnr R h ρ) = (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)).det := by sorry
