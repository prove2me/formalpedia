-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_Chart_norm_le
-- name    : PI.SwSandwichOfWork.Chart_norm_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:31.561139+00:00
-- url     : https://prove2.me/theorems/88de9f2a-dc5c-5d08-8f18-58d670771595
-- title:
--   Sw Sandwich Of Work: Chart norm le
-- statement:
--   The Sw Sandwich Of Work construction uses the Chart norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/ChartZeroEqOneOfLongWeylSq.lean#L73-L90

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

theorem PI.SwSandwichOfWork.Chart_norm_le (hN : NormRL) (hLI : LIso) {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r}
    (hv : v ∈ Vs k r) : ‖v‖ ≤ ‖Lm k r v‖ := by sorry
