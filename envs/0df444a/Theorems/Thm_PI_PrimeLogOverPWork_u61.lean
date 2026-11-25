-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_u61
-- name    : PI.PrimeLogOverPWork.u61
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:40.190618+00:00
-- url     : https://prove2.me/theorems/fcd02aaf-8c79-4d76-b8af-5a70f01d1deb
-- title:
--   Prime Log Over PWork: u61
-- statement:
--   The Prime Log Over PWork construction uses the u61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L87-L90

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

theorem PI.PrimeLogOverPWork.u61 : Real.log (61 : ℝ) ≤ 119 / 20 * Real.log 2 := by sorry
