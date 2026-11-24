-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_step
-- name    : PI.UnitaryGroupMassFormula.QmMove.step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:57.15293+00:00
-- url     : https://prove2.me/theorems/f5c96208-0e41-4de9-a17b-b1c28572a676
-- title:
--   Qm Move: step
-- statement:
--   The Qm Move construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L29-L46

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

theorem PI.UnitaryGroupMassFormula.QmMove.step {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (P Q X : Equiv.Perm (Fin t) → A)
    (hX : ∀ τ, X (τ * s) = X τ) (hPQ : ∀ τ, P (τ * s) - Q τ = X τ) :
    ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Q τ = -∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ := by sorry
