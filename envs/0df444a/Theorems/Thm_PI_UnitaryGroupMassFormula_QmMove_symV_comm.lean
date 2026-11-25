-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_symV_comm
-- name    : PI.UnitaryGroupMassFormula.QmMove.symV_comm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:14.275995+00:00
-- url     : https://prove2.me/theorems/bd2f5a3d-0581-4c6e-b772-1e4ff98cc456
-- title:
--   Qm Move: sym V comm
-- statement:
--   The Qm Move construction uses the sym V comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L51-L52

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)
omit [Algebra ℂ A]

theorem PI.UnitaryGroupMassFormula.QmMove.symV_comm (x c d : Fin n) : symV y x c d = symV y x d c := by sorry
