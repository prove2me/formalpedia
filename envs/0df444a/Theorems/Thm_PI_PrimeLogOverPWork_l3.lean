-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_l3
-- name    : PI.PrimeLogOverPWork.l3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:05.445805+00:00
-- url     : https://prove2.me/theorems/50302d64-07f3-494b-98aa-cfdd14b8887f
-- title:
--   Prime Log Over PWork: l3
-- statement:
--   The Prime Log Over PWork construction uses the l3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L92-L95

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

theorem PI.PrimeLogOverPWork.l3 : (31 : ℝ) / 20 * Real.log 2 ≤ Real.log (3 : ℝ) := by sorry
