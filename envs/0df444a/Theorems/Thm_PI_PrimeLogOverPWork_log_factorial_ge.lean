-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_ge
-- name    : PI.PrimeLogOverPWork.log_factorial_ge
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:48.326871+00:00
-- url     : https://prove2.me/theorems/2ab0e63e-f13e-41e0-aff5-fba3f9d098f1
-- title:
--   Prime Log Over PWork: log factorial ge
-- statement:
--   The Prime Log Over PWork construction uses the log factorial ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L77-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L77-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
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

theorem PI.PrimeLogOverPWork.log_factorial_ge (n : ℕ) (hn : 27 ≤ n) :
    (n : ℝ) * S n - Chebyshev.theta n
      + (Real.log 2 * ((n : ℝ) * (7 / 16) - 3) + Real.log 3 * ((n : ℝ) * (4 / 27) - 2)
      + Real.log 5 * ((n : ℝ) / 25 - 1)) ≤ Real.log (n ! : ℝ) := by sorry
