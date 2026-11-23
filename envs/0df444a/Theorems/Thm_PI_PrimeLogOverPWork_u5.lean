-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_u5
-- name    : PI.PrimeLogOverPWork.u5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:23.79342+00:00
-- url     : https://prove2.me/theorems/b60e1c97-b339-4dc8-a16b-8b5cfa9eb70c
-- title:
--   Prime Log Over PWork: u5
-- statement:
--   The Prime Log Over PWork construction uses the u5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L12-L15

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

theorem PI.PrimeLogOverPWork.u5 : Real.log (5 : ℝ) ≤ 47 / 20 * Real.log 2 := by sorry
