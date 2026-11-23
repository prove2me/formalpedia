-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_u17
-- name    : PI.PrimeLogOverPWork.u17
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:54.701397+00:00
-- url     : https://prove2.me/theorems/3af17a68-bf74-49ac-9810-1eb9ceb3b4e5
-- title:
--   Prime Log Over PWork: u17
-- statement:
--   The Prime Log Over PWork construction uses the u17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L32-L35

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

theorem PI.PrimeLogOverPWork.u17 : Real.log (17 : ℝ) ≤ 82 / 20 * Real.log 2 := by sorry
