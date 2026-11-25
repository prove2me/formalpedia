-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_neg_one_pow_sub
-- name    : PI.UnitaryGroupMassFormula.QmMove.neg_one_pow_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:08.657873+00:00
-- url     : https://prove2.me/theorems/c5fd3bb9-0239-4a1f-8af3-ceada534e7b6
-- title:
--   Qm Move: neg one pow sub
-- statement:
--   The Qm Move construction uses the neg one pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L118-L121

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
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

theorem PI.UnitaryGroupMassFormula.QmMove.neg_one_pow_sub (m j : ℕ) (hj : j ≤ m) :
    ((-1 : ℤ) ^ (m - j) : ℤ) = (-1) ^ m * (-1) ^ j := by sorry
