-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_extN_lt
-- name    : PI.UnitaryGroupMassFormula.QmMove.extN_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:39.314371+00:00
-- url     : https://prove2.me/theorems/302fe344-523d-4ec2-9b72-ca304d6ed74c
-- title:
--   Qm Move: ext N lt
-- statement:
--   The Qm Move construction uses the ext N lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/MoveOperatorCovariance.lean#L12-L13

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

theorem PI.UnitaryGroupMassFormula.QmMove.extN_lt {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : Fin m) : extN b d k = b k := by sorry
