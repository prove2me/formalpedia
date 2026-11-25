-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_phiL_last
-- name    : PI.UnitaryGroupMassFormula.QmMove.phiL_last
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:21.141647+00:00
-- url     : https://prove2.me/theorems/2683e12d-5a60-59a2-aca7-cfdad34577ab
-- title:
--   Qm Move: phi L last
-- statement:
--   The Qm Move construction uses the phi L last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L102-L104

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

theorem PI.UnitaryGroupMassFormula.QmMove.phiL_last (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    lastColumnSplit m (j, ρ) (Fin.last m) = j := by sorry
