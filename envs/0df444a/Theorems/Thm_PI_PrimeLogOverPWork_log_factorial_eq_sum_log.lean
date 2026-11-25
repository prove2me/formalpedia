-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_eq_sum_log
-- name    : PI.PrimeLogOverPWork.log_factorial_eq_sum_log
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:40.719483+00:00
-- url     : https://prove2.me/theorems/fc28939c-d4c5-5915-b34a-c2c51b67d659
-- title:
--   Prime Log Over PWork: log factorial eq sum log
-- statement:
--   The Prime Log Over PWork construction uses the log factorial eq sum log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L21-L28

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

theorem PI.PrimeLogOverPWork.log_factorial_eq_sum_log (n : ℕ) :
    Real.log (n ! : ℝ) = ∑ k ∈ Ioc 0 n, Real.log (k : ℝ) := by sorry
