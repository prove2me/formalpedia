-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_mul_le_two_mul_sum_min_add
-- name    : SumOfSetsInSeveralDimensions.two_mul_mul_le_two_mul_sum_min_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:27.716475+00:00
-- url     : https://prove2.me/theorems/9fdc3574-8eb9-5380-812c-57f19c5b44b3
-- title:
--   Sum Of Sets In Several Dimensions: two mul mul le two mul sum min add
-- statement:
--   For `1 ≤ m ≤ n`, twice the sum `∑ t ∈ {1, …, m - 1}, min d (n - t)` is at least
--   `2 * d * m - d * (d + 1)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L64-L67
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L64-L67

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise

theorem SumOfSetsInSeveralDimensions.two_mul_mul_le_two_mul_sum_min_add (d : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    2 * (d * m) ≤ 2 * ∑ t ∈ Icc 1 (m - 1), min d (n - t) + d * (d + 1) := by sorry
