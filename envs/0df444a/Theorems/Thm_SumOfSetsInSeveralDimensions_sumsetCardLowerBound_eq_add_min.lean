-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq_add_min
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_eq_add_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:09.72014+00:00
-- url     : https://prove2.me/theorems/21fae11f-4e29-495a-9ed4-fce3b84310ea
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound eq add min
-- statement:
--   `G_d(m, n) = G_d(m - 1, n - 1) + min (d + 1) n` for `m ≥ 2`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L54-L60
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundFunction.lean#L54-L60

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

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_eq_add_min {d m n : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m n = sumsetCardLowerBound d (m - 1) (n - 1) + min (d + 1) n := by sorry
