-- Prove2me | Theorems.Thm_PI_PrimeLogOverPWork_term_ge
-- name    : PI.PrimeLogOverPWork.term_ge
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:36:51.983654+00:00
-- url     : https://prove2.me/theorems/3c9bd779-1211-48b4-b34d-d71ba39a11ed
-- title:
--   Prime Log Over PWork: term ge
-- statement:
--   The Prime Log Over PWork construction uses the term ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/PrimeLogOverPWork.lean#L34-L35

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

theorem PI.PrimeLogOverPWork.term_ge (n d : ℕ) : Λ d * ((n : ℝ) / d - 1) ≤ Λ d * ((n / d : ℕ) : ℝ) := by sorry
