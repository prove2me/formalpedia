-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Pv_last
-- name    : PI.UnitaryGroupMassFormula.QmMove.Pv_last
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:54.343664+00:00
-- url     : https://prove2.me/theorems/bad2feee-f41d-410a-8367-0d78653bd658
-- title:
--   Qm Move: Pv last
-- statement:
--   The Qm Move construction uses the Pv last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L132-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermsSignSquared.lean#L132-L145

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

theorem PI.UnitaryGroupMassFormula.QmMove.Pv_last (τ : Equiv.Perm (Fin (m + 1))) :
    Pv E y a b w m τ = qminor E a (fun k => b (τ k.castSucc)) (w - 1) * y (b (τ (Fin.last m))) := by sorry
