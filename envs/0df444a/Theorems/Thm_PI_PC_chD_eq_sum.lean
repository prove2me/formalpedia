-- Prove2me | Theorems.Thm_PI_PC_chD_eq_sum
-- name    : PI.PC.chD_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:56.090566+00:00
-- url     : https://prove2.me/theorems/35ccb6df-0448-499e-a6d8-430f1487d1c3
-- title:
--   PC: ch D eq sum
-- statement:
--   The PC construction uses the ch D eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean#L82-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean#L82-L106

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

theorem PI.PC.chD_eq_sum (x : ℝ) : chD x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by sorry
