-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_strict_right_case
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_strict_right_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:20.800968+00:00
-- url     : https://prove2.me/theorems/4f64068c-826a-5043-bb3b-a4aede9ba23c
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound of strict right case
-- statement:
--   The case in which one point is removed from the strictly larger set and the dimension drops
--   by one: the sumset loses at least `m` points.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L105-L109
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L105-L109

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

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_strict_right_case {d m n p s : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (hrec : sumsetCardLowerBound (d - 1) m (n - 1) ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by sorry
