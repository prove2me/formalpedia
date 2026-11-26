-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:28.495609+00:00
-- url     : https://prove2.me/theorems/ae676b47-3216-45bb-97e7-f52312e1b864
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound eq
-- statement:
--   The definition of `sumsetCardLowerBound`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L37-L39
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L37-L39

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

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_eq (d m n : ℕ) :
    sumsetCardLowerBound d m n = n + ∑ t ∈ Icc 1 (m - 1), min d (n - t) := by sorry
