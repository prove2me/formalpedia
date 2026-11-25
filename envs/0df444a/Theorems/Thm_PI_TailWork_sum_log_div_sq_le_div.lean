-- Prove2me | Theorems.Thm_PI_TailWork_sum_log_div_sq_le_div
-- name    : PI.TailWork.sum_log_div_sq_le_div
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:50.436822+00:00
-- url     : https://prove2.me/theorems/b1953b40-7654-577e-9c26-8e6dae633a7c
-- title:
--   Tail Work: sum log div sq le div
-- statement:
--   The Tail Work construction uses the sum log div sq le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogDivSqLeDiv.lean#L72-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PrimeLogarithmTail/SumLogDivSqLeDiv.lean#L72-L110

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PrimeLogarithmTail_SumLogDivSqLeDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.TailWork
open Finset

theorem PI.TailWork.sum_log_div_sq_le_div (X : ℝ) (hX : 0 < X) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X := by sorry
