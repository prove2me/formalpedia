-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_sum_expo
-- name    : PI.OddDualWeyl.LowA.sum_expo
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:49.941133+00:00
-- url     : https://prove2.me/theorems/fa86277b-5cc6-57e6-b72f-8de329f186de
-- title:
--   Low A: sum expo
-- statement:
--   The Low A construction uses the sum expo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L85-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L85-L135

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

theorem PI.OddDualWeyl.LowA.sum_expo {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∑ s : Fin (m + 1), s.val * (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = expM lam := by sorry
