-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_prod_diff
-- name    : PI.UnitaryGroupMassFormula.QmMove.prod_diff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:16.564854+00:00
-- url     : https://prove2.me/theorems/4c75e768-511f-5771-be85-daf225c18b88
-- title:
--   Qm Move: prod diff
-- statement:
--   The Qm Move construction uses the prod diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CovariantVectorMove/SumPermEqSumFirstColumnSplit.lean#L12-L20

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

theorem PI.UnitaryGroupMassFormula.QmMove.prod_diff {A : Type*} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn f).prod - (List.ofFn g).prod =
      ((List.ofFn f).take i).prod *
        (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩ - g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
        ((List.ofFn f).drop (i + 2)).prod := by sorry
