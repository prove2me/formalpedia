-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_prod_minors
-- name    : PI.OddDualWeyl.LowA.prod_minors
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:53.612278+00:00
-- url     : https://prove2.me/theorems/7be9b724-f017-5ee5-bc48-6a6e0866589c
-- title:
--   Low A: prod minors
-- statement:
--   The Low A construction uses the prod minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L56-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
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
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.LowA.prod_minors {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1))) :
    ∏ s : Fin (m + 1), pMinor R σ (m + 1 - 1 - s.val) (by omega) ^
      (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = pw R σ (nuOf lam) := by sorry
