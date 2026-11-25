-- Prove2me | Theorems.Thm_PI_PC_log_factorial_eq_sum_log
-- name    : PI.PC.log_factorial_eq_sum_log
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:39.507108+00:00
-- url     : https://prove2.me/theorems/6eee2836-8da8-56f0-b09b-f2310f41e8e4
-- title:
--   PC: log factorial eq sum log
-- statement:
--   The PC construction uses the log factorial eq sum log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean#L12-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta

theorem PI.PC.log_factorial_eq_sum_log (N : ℕ) : log ((N ! : ℕ) : ℝ) = ∑ m ∈ Ioc 0 N, log (m : ℝ) := by sorry
