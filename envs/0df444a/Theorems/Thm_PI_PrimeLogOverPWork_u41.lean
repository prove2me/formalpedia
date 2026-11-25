-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_u41
-- name    : PI.PrimeLogOverPWork.u41
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:58.252265+00:00
-- url     : https://prove2.me/theorems/6a66b40f-a9ff-516b-a7c4-2e4d79608fbf
-- title:
--   Prime Log Over PWork: u41
-- statement:
--   The Prime Log Over PWork construction uses the u41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L62-L65

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

theorem PI.PrimeLogOverPWork.u41 : Real.log (41 : ℝ) ≤ 108 / 20 * Real.log 2 := by sorry
