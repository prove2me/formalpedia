-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_pMinor_eq
-- name    : PI.OddDualWeyl.Low.pMinor_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:52.354769+00:00
-- url     : https://prove2.me/theorems/413051cc-0e39-4c75-87bc-ebca7192378f
-- title:
--   Low: p Minor eq
-- statement:
--   The Low construction uses the p Minor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L16-L17

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

theorem PI.OddDualWeyl.Low.pMinor_eq {k : ℕ} (σ : Equiv.Perm (Fin k)) (n : ℕ) (h : n ≤ k) :
    pMinor R σ n h = mnr R h (σ ∘ Fin.castLE h) := by sorry
