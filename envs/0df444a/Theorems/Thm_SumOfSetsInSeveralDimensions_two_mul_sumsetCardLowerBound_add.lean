-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_sumsetCardLowerBound_add
-- name    : SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:09.963818+00:00
-- url     : https://prove2.me/theorems/9108be17-afd2-43da-926b-93fbb50c4404
-- title:
--   Sum Of Sets In Several Dimensions: two mul sumset Card Lower Bound add
-- statement:
--   **Formula (1.6), first form.** If `m ≤ n < m + d` and `d < n`, then
--   `2 * G_d(m, n) + (d - t) * (d - t - 1) = 2 * (n + d * (m - 1))`, where `t = n - m`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L72-L82
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBoundValues.lean#L72-L82

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

theorem SumOfSetsInSeveralDimensions.two_mul_sumsetCardLowerBound_add (hmn : m ≤ n) (hnm : n < m + d) (hdn : d < n) :
    2 * sumsetCardLowerBound d m n + (d - (n - m)) * (d - (n - m) - 1) =
      2 * (n + d * (m - 1)) := by sorry
