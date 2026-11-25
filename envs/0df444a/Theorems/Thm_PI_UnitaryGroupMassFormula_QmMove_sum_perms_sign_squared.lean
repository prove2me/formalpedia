-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sum_perms_sign_squared
-- name    : PI.UnitaryGroupMassFormula.QmMove.sum_perms_sign_squared
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:05.854291+00:00
-- url     : https://prove2.me/theorems/140e4764-f6ee-4ac2-9bab-2fdb1a521638
-- title:
--   Qm Move: sum perms sign squared
-- statement:
--   The Qm Move construction uses the sum perms sign squared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L20-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove

theorem PI.UnitaryGroupMassFormula.QmMove.sum_perms_sign_squared {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (m.factorial : A) * ((z : A) * (D * x)) := by sorry
