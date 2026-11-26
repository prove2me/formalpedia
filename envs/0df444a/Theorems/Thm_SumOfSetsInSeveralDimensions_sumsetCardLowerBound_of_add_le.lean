-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_add_le
-- name    : SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:58.935641+00:00
-- url     : https://prove2.me/theorems/3dbba2aa-0b61-5941-afe4-5458b182e5f8
-- title:
--   Sum Of Sets In Several Dimensions: sumset Card Lower Bound of add le
-- statement:
--   **Formula (1.5).** If `m + d ≤ n + 1`, then `G_d(m, n) = n + d * (m - 1)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L46-L49
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L46-L49

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

theorem SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_add_le (h : m + d ≤ n + 1) :
    sumsetCardLowerBound d m n = n + d * (m - 1) := by sorry
