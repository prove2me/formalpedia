-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_rho_sum
-- name    : PI.UnitaryGroupMassFormula.QmMove.rho_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:48.165059+00:00
-- url     : https://prove2.me/theorems/9d7f7904-5332-4d97-b363-28e3ef74a87b
-- title:
--   Qm Move: rho sum
-- statement:
--   The Qm Move construction uses the rho sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L9-L18

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

theorem PI.UnitaryGroupMassFormula.QmMove.rho_sum {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (m.factorial : A) * ((z : A) * (x * D)) := by sorry
