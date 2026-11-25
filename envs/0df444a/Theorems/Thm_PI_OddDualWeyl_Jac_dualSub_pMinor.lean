-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Jac_dualSub_pMinor
-- name    : PI.OddDualWeyl.Jac.dualSub_pMinor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:13.834083+00:00
-- url     : https://prove2.me/theorems/796b7101-fd92-5942-b15a-78bb56ab850e
-- title:
--   Jac: dual Sub p Minor
-- statement:
--   The Jac construction uses the dual Sub p Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacobiMinorIdentity.lean#L131-L137

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity
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
open PI PI.OddDualWeyl PI.OddDualWeyl.Jac

theorem PI.OddDualWeyl.Jac.dualSub_pMinor (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ)
    (hs : s ≤ k) :
    dualSub R k (pMinor R σ s hs) =
      (Matrix.of fun p q : Fin s =>
        adjugate (genM R k) (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by sorry
