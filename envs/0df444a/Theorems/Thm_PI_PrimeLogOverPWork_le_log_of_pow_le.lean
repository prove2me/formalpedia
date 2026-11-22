-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_le_log_of_pow_le
-- name    : PI.PrimeLogOverPWork.le_log_of_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:41.642825+00:00
-- url     : https://prove2.me/theorems/2a00b40d-2c03-4cad-9bf3-0739eac0bf7c
-- title:
--   Prime Log Over PWork: le log of pow le
-- statement:
--   The Prime Log Over PWork construction uses the le log of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L82-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L82-L96

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

theorem PI.PrimeLogOverPWork.le_log_of_pow_le (p a b : ℕ) (hb : 0 < b) (h : 2 ^ a ≤ p ^ b) :
    (a : ℝ) / b * Real.log 2 ≤ Real.log (p : ℝ) := by sorry
