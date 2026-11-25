-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_phiL_sign
-- name    : PI.UnitaryGroupMassFormula.QmMove.phiL_sign
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:59.306293+00:00
-- url     : https://prove2.me/theorems/e329b715-9665-407c-8421-7e4dfe859c62
-- title:
--   Qm Move: phi L sign
-- statement:
--   The Qm Move construction uses the phi L sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L106-L108

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

theorem PI.UnitaryGroupMassFormula.QmMove.phiL_sign (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (lastColumnSplit m (j, ρ)) = (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign ρ := by sorry
