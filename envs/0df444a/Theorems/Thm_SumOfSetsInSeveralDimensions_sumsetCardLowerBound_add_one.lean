-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_add_one
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:58.726964+00:00
-- url     : https://prove2.me/theorems/ffd85362-fda8-4b3a-a51e-ebb4be07bc8f
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound add one
-- statement:
--   `G_d(m + 1, n) = G_d(m, n) + min d (n - m)` for `m ≥ 1`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L38-L43
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L38-L43

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

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_add_one (hm : 1 ≤ m) :
    sumsetCardLowerBound d (m + 1) n = sumsetCardLowerBound d m n + min d (n - m) := by sorry
