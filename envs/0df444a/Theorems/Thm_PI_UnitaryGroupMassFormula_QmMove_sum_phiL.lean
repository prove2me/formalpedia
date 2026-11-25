-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sum_phiL
-- name    : PI.UnitaryGroupMassFormula.QmMove.sum_phiL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:39.161842+00:00
-- url     : https://prove2.me/theorems/bdde9931-b414-44bc-be96-8c4220c2dcb6
-- title:
--   Qm Move: sum phi L
-- statement:
--   The Qm Move construction uses the sum phi L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L93-L96

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

theorem PI.UnitaryGroupMassFormula.QmMove.sum_phiL {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (lastColumnSplit m (j, ρ)) := by sorry
