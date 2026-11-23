-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sgnlem
-- name    : PI.UnitaryGroupMassFormula.QmMove.sgnlem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:20.763226+00:00
-- url     : https://prove2.me/theorems/d55782b8-54e0-412c-8852-dd77f5d667da
-- title:
--   Qm Move: sgnlem
-- statement:
--   The Qm Move construction uses the sgnlem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L15-L17

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

theorem PI.UnitaryGroupMassFormula.QmMove.sgnlem {A : Type*} [Ring A] (z z' : ℤ) (x y : A) :
    ((z * z' : ℤ) : A) * (x * y) = (z : A) * (x * ((z' : A) * y)) := by sorry
