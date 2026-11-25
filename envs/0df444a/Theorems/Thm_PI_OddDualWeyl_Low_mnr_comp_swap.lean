-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_mnr_comp_swap
-- name    : PI.OddDualWeyl.Low.mnr_comp_swap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:21.007389+00:00
-- url     : https://prove2.me/theorems/59cf17b9-6252-5557-90e7-18e908e0068e
-- title:
--   Low: mnr comp swap
-- statement:
--   The Low construction uses the mnr comp swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L85-L93

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

theorem PI.OddDualWeyl.Low.mnr_comp_swap {k n : ℕ} (h : n ≤ k) (ρ : Fin n → Fin k) (p q : Fin n) (hpq : p ≠ q) :
    mnr R h (ρ ∘ Equiv.swap p q) = - mnr R h ρ := by sorry
