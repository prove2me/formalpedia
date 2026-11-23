-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_u13
-- name    : PI.PrimeLogOverPWork.u13
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:44.596539+00:00
-- url     : https://prove2.me/theorems/363cc7ef-57d3-41c3-ab49-0217372ce944
-- title:
--   Prime Log Over PWork: u13
-- statement:
--   The Prime Log Over PWork construction uses the u13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/SLeOfBlock.lean#L27-L30

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

theorem PI.PrimeLogOverPWork.u13 : Real.log (13 : ℝ) ≤ 75 / 20 * Real.log 2 := by sorry
