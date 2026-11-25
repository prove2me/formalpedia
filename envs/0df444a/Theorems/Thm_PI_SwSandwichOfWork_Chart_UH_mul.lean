-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_Chart_UH_mul
-- name    : PI.SwSandwichOfWork.Chart_UH_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:42:04.273874+00:00
-- url     : https://prove2.me/theorems/a3311f49-6021-45ae-8cec-4422baf40b01
-- title:
--   Sw Sandwich Of Work: Chart UH mul
-- statement:
--   The Sw Sandwich Of Work construction uses the Chart UH mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L37-L43

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

theorem PI.SwSandwichOfWork.Chart_UH_mul {A B : Mat k r} (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r)) :
    A * B ∈ UH (Hpk k r) := by sorry
