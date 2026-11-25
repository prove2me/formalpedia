-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sgn_mul_swap
-- name    : PI.UnitaryGroupMassFormula.QmMove.sgn_mul_swap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:34.263698+00:00
-- url     : https://prove2.me/theorems/aa1a88ee-7d11-42d7-bbe1-994fad7ed388
-- title:
--   Qm Move: sgn mul swap
-- statement:
--   The Qm Move construction uses the sgn mul swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L22-L27

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

theorem PI.UnitaryGroupMassFormula.QmMove.sgn_mul_swap {A : Type*} [Ring A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by sorry
