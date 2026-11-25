-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sum_perm_eq_sum_firstColumnSplit
-- name    : PI.UnitaryGroupMassFormula.QmMove.sum_perm_eq_sum_firstColumnSplit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:24.344872+00:00
-- url     : https://prove2.me/theorems/bd2c1ade-a4a2-4174-9bcc-1e021c289d24
-- title:
--   Qm Move: sum perm eq sum first Column Split
-- statement:
--   The Qm Move construction uses the sum perm eq sum first Column Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L88-L91

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

theorem PI.UnitaryGroupMassFormula.QmMove.sum_perm_eq_sum_firstColumnSplit {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (phi0 m (j, ρ)) := by sorry
