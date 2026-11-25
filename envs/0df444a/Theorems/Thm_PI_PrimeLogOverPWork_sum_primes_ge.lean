-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_sum_primes_ge
-- name    : PI.PrimeLogOverPWork.sum_primes_ge
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:18:30.483816+00:00
-- url     : https://prove2.me/theorems/bb68dcd7-2e30-4b52-9b32-945d8e312d3b
-- title:
--   Prime Log Over PWork: sum primes ge
-- statement:
--   The Prime Log Over PWork construction uses the sum primes ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L65-L75

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

theorem PI.PrimeLogOverPWork.sum_primes_ge (n : ℕ) :
    (n : ℝ) * S n - Chebyshev.theta n
      ≤ ∑ d ∈ Ioc 0 n with d.Prime, Λ d * ((n / d : ℕ) : ℝ) := by sorry
