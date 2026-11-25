-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_expo_last
-- name    : PI.OddDualWeyl.LowA.expo_last
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:27.775456+00:00
-- url     : https://prove2.me/theorems/a303c203-7dd5-457a-97a2-fe004601a221
-- title:
--   Low A: expo last
-- statement:
--   The Low A construction uses the expo last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L51-L54

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

theorem PI.OddDualWeyl.LowA.expo_last {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf lam (Fin.last m) - nuNext (nuOf lam) (Fin.last m) = 0 := by sorry
