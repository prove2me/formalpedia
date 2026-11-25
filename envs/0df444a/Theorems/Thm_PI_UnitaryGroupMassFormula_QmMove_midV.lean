-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_midV
-- name    : PI.UnitaryGroupMassFormula.QmMove.midV
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:35.995166+00:00
-- url     : https://prove2.me/theorems/2164fa37-7439-4ced-af53-0deaa05ed2c6
-- title:
--   Qm Move: mid V
-- statement:
--   The Qm Move construction uses the mid V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L54-L65

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

theorem PI.UnitaryGroupMassFormula.QmMove.midV (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    y c * Tm E v x d - Tm E v' x d * y c = symV y x c d := by sorry
