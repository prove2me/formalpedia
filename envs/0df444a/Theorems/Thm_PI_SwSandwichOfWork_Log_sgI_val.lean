-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_Log_sgI_val
-- name    : PI.SwSandwichOfWork.Log_sgI_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:05.787313+00:00
-- url     : https://prove2.me/theorems/5353a755-8f68-5b6c-aaa0-55ab69d73f5e
-- title:
--   Sw Sandwich Of Work: Log sg I val
-- statement:
--   The Sw Sandwich Of Work construction uses the Log sg I val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/UnrealifyRL.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/UnrealifyRL.lean#L50-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}

theorem PI.SwSandwichOfWork.Log_sgI_val (i : Fin (2 * r + k + 1)) : ((sgI k r i).val = r + k ↔ i.val = r + k) := by sorry
