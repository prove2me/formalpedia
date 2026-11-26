-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_equal_right_case
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_equal_right_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:18.794247+00:00
-- url     : https://prove2.me/theorems/7e66bf05-7858-5486-91b9-049839265c4b
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound of equal right case
-- statement:
--   The case in which the sets have the same size `m`, one point is removed from one of them and
--   the dimension drops by one: the sumset loses at least `m` points.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L98-L101
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L98-L101

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_equal_right_case {d m p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) m ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m m ≤ s := by sorry
