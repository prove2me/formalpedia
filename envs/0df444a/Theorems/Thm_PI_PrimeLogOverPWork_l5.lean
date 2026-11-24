-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_l5
-- name    : PI.PrimeLogOverPWork.l5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:24.596852+00:00
-- url     : https://prove2.me/theorems/88ea5d17-be6e-47b8-86af-574ce0bea501
-- title:
--   Prime Log Over PWork: l5
-- statement:
--   The Prime Log Over PWork construction uses the l5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L97-L100

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset

theorem PI.PrimeLogOverPWork.l5 : (46 : ℝ) / 20 * Real.log 2 ≤ Real.log (5 : ℝ) := by sorry
