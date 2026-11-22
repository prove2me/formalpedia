-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_log_le_of_pow_le
-- name    : PI.PrimeLogOverPWork.log_le_of_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:27.1059+00:00
-- url     : https://prove2.me/theorems/ec823593-c577-4419-99f2-9b7bc0420b42
-- title:
--   Prime Log Over PWork: log le of pow le
-- statement:
--   The Prime Log Over PWork construction uses the log le of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean#L72-L80

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

theorem PI.PrimeLogOverPWork.log_le_of_pow_le (p a b : ℕ) (hp : 0 < p) (hb : 0 < b) (h : p ^ b ≤ 2 ^ a) :
    Real.log (p : ℝ) ≤ (a : ℝ) / b * Real.log 2 := by sorry
