-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_midC
-- name    : PI.UnitaryGroupMassFormula.QmMove.midC
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:41:03.188928+00:00
-- url     : https://prove2.me/theorems/da66cecb-6c3a-5e6c-bcf2-eb89f6d41bb3
-- title:
--   Qm Move: mid C
-- statement:
--   The Qm Move construction uses the mid C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L33-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L33-L52

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

theorem PI.UnitaryGroupMassFormula.QmMove.midC (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    η c * Tm E v' x d - Tm E v x d * η c = -symC η d x c := by sorry
