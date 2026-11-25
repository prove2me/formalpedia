-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_sum_E_ge
-- name    : PI.PrimeLogOverPWork.sum_E_ge
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:50.056637+00:00
-- url     : https://prove2.me/theorems/efa3b9d0-9b8f-44d6-a4f4-4716b15ee82d
-- title:
--   Prime Log Over PWork: sum E ge
-- statement:
--   The Prime Log Over PWork construction uses the sum E ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L42-L59

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

theorem PI.PrimeLogOverPWork.sum_E_ge (n : ℕ) :
    Real.log 2 * ((n : ℝ) * (7 / 16) - 3) + Real.log 3 * ((n : ℝ) * (4 / 27) - 2)
      + Real.log 5 * ((n : ℝ) / 25 - 1) ≤ ∑ d ∈ E, Λ d * ((n / d : ℕ) : ℝ) := by sorry
