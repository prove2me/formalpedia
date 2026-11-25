-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_le
-- name    : PI.PrimeLogOverPWork.log_factorial_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:48.526995+00:00
-- url     : https://prove2.me/theorems/c08dad01-8b06-5e95-87f8-527b583289ef
-- title:
--   Prime Log Over PWork: log factorial le
-- statement:
--   The Prime Log Over PWork construction uses the log factorial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L48-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat

theorem PI.PrimeLogOverPWork.log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n ! : ℝ) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by sorry
