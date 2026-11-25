-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sign_firstColumnSplit
-- name    : PI.UnitaryGroupMassFormula.QmMove.sign_firstColumnSplit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:33.682873+00:00
-- url     : https://prove2.me/theorems/97fce7bf-c9ce-4b80-891b-01353aa1f16c
-- title:
--   Qm Move: sign first Column Split
-- statement:
--   The Qm Move construction uses the sign first Column Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L67-L70

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

theorem PI.UnitaryGroupMassFormula.QmMove.sign_firstColumnSplit (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m (j, ρ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign ρ := by sorry
