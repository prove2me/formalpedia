-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_full_case
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_full_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:13.214812+00:00
-- url     : https://prove2.me/theorems/0e31f10c-2ae6-40c7-ae43-4271101d41d8
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound of full case
-- statement:
--   The case in which one point is removed from each set and the dimension does not change: the
--   sumset loses at least `d + 1` points.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L76-L79
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L76-L79

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

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_full_case {d m n p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound d (m - 1) (n - 1) ≤ p) (hcard : p + d + 1 ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by sorry
