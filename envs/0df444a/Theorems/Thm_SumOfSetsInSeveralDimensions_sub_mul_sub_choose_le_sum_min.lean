-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sub_mul_sub_choose_le_sum_min
-- name    : SumOfSetsInSeveralDimensions.sub_mul_sub_choose_le_sum_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:30.031835+00:00
-- url     : https://prove2.me/theorems/ec137da9-719c-4707-b9be-e515c2d70e63
-- title:
--   Sum Of Sets In Several Dimensions: sub mul sub choose le sum min
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the sub mul sub choose le sum min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L201-L215
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L201-L215

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section

theorem SumOfSetsInSeveralDimensions.sub_mul_sub_choose_le_sum_min (b r : ℕ) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) := by sorry
