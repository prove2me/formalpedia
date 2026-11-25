-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Nc_last
-- name    : PI.UnitaryGroupMassFormula.QmMove.Nc_last
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:35.731801+00:00
-- url     : https://prove2.me/theorems/df7f3500-2b97-4a91-90b3-ee83812b4977
-- title:
--   Qm Move: Nc last
-- statement:
--   The Qm Move construction uses the Nc last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L228-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L228-L261

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)

theorem PI.UnitaryGroupMassFormula.QmMove.Nc_last : Nc E η a b w m = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E (a ∘ j.succAbove) b w * η (a j)) := by sorry
