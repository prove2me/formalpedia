-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_sumsetCardLowerBound_of_le
-- name    : SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:20.491779+00:00
-- url     : https://prove2.me/theorems/443d5c9f-117a-4acc-aeb6-ff2e854e1263
-- title:
--   Sum Of Sets In Several Dimensions: two mul sumset Card Lower Bound of le
-- statement:
--   **Formula (1.7).** If `1 ≤ m ≤ n ≤ d`, then `2 * G_d(m, n) = 2 * n + (m - 1) * (2 * n - m)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L85-L96
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L85-L96

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
variable {d m n : ℕ}

theorem SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_of_le (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : n ≤ d) :
    2 * sumsetCardLowerBound d m n = 2 * n + (m - 1) * (2 * n - m) := by sorry
