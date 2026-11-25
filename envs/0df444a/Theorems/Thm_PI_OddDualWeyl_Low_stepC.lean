-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Low_stepC
-- name    : PI.OddDualWeyl.Low.stepC
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:20.684111+00:00
-- url     : https://prove2.me/theorems/12a83d74-669d-5a08-af27-12e64e5c0407
-- title:
--   Low: step C
-- statement:
--   The Low construction uses the step C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L172-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/MnrUpdateEqZero.lean#L172-L193

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
variable {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)

theorem PI.OddDualWeyl.Low.stepC (s : Fin (n + 1)) (hs : i.val < s.val) :
    rowGen R (σ i.succ) (σ i.castSucc) (pMinor R σ (s.val + 1) s.isLt) =
      Polynomial.C (pMinor R σ (s.val + 1) s.isLt) ∧
    pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt = - pMinor R σ (s.val + 1) s.isLt := by sorry
