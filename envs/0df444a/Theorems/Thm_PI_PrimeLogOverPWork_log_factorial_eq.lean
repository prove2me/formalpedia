-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_eq
-- name    : PI.PrimeLogOverPWork.log_factorial_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:42.257405+00:00
-- url     : https://prove2.me/theorems/b34f251f-120a-5bdc-b8e1-627e56dc645d
-- title:
--   Prime Log Over PWork: log factorial eq
-- statement:
--   The Prime Log Over PWork construction uses the log factorial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L30-L46

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

theorem PI.PrimeLogOverPWork.log_factorial_eq (n : ℕ) :
    Real.log (n ! : ℝ) = ∑ d ∈ Ioc 0 n, Λ d * ((n / d : ℕ) : ℝ) := by sorry
