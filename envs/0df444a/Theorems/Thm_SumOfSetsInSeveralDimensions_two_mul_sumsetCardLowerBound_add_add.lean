-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_sumsetCardLowerBound_add_add
-- name    : SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_add_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:59.430067+00:00
-- url     : https://prove2.me/theorems/03435e69-7c36-566f-83bf-7e897e854c83
-- title:
--   Sum Of Sets In Several Dimensions: two mul sumset Card Lower Bound add add
-- statement:
--   **Formula (1.6).** If `m ≤ n < m + d` and `d < n`, then
--   `2 * G_d(m, n) + d * (d + 1) + (n - m) * (n - m + 1) = 2 * n * (d + 1)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L53-L68
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L53-L68

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

theorem SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_add_add (hmn : m ≤ n) (hnm : n < m + d) (hdn : d < n) :
    2 * sumsetCardLowerBound d m n + d * (d + 1) + (n - m) * (n - m + 1) = 2 * n * (d + 1) := by sorry
