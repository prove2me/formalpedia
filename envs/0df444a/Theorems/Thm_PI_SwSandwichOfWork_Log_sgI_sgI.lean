-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_Log_sgI_sgI
-- name    : PI.SwSandwichOfWork.Log_sgI_sgI
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:29.007068+00:00
-- url     : https://prove2.me/theorems/f435555d-dd69-44a5-8593-1c1e9f39601a
-- title:
--   Sw Sandwich Of Work: Log sg I sg I
-- statement:
--   The Sw Sandwich Of Work construction uses the Log sg I sg I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/UnrealifyRL.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/UnrealifyRL.lean#L46-L48

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

theorem PI.SwSandwichOfWork.Log_sgI_sgI (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i) = i := by sorry
