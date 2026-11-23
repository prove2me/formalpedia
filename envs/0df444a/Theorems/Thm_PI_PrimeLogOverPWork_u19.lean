-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_u19
-- name    : PI.PrimeLogOverPWork.u19
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:19.528746+00:00
-- url     : https://prove2.me/theorems/a37fd709-894b-47ef-856c-367b138cba94
-- title:
--   Prime Log Over PWork: u19
-- statement:
--   The Prime Log Over PWork construction uses the u19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L37-L40

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

theorem PI.PrimeLogOverPWork.u19 : Real.log (19 : ℝ) ≤ 85 / 20 * Real.log 2 := by sorry
