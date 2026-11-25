-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_Chart_core
-- name    : PI.SwSandwichOfWork.Chart_core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:39.591689+00:00
-- url     : https://prove2.me/theorems/a6c0804a-ed65-482f-8e0f-78328b7bfd99
-- title:
--   Sw Sandwich Of Work: Chart core
-- statement:
--   The Sw Sandwich Of Work construction uses the Chart core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L92-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L92-L139

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}

theorem PI.SwSandwichOfWork.Chart_core (hN : NormRL) (hLog : LogG) (hW : LongWeylElementSquare) (hBC : BigCellG) (hPF : PhiForm)
    (hPD : PhiDeriv) (hLW : LieWb) (hEN : ExpN) (hLI : LIso) (k r : ℕ) :
    ∃ F : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r → Mat k r, HasStrictFDerivAt F (Lm k r) 0 ∧
      F 0 = 0 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Vs k r, ‖v‖ < δ →
        F v ∈ uH k r ∧ NormedSpace.exp (F v) = PhiP k r v ∧ ‖F v - Lm k r v‖ ≤ η * ‖Lm k r v‖ := by sorry
