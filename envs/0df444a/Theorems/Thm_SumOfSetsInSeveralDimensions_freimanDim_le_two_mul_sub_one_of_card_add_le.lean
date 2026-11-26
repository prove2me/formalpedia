-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_freimanDim_le_two_mul_sub_one_of_card_add_le
-- name    : SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:07.412325+00:00
-- url     : https://prove2.me/theorems/7e6c92a2-482d-596f-84ef-4b79f9f2aac0
-- title:
--   Sum Of Sets In Several Dimensions: freiman Dim le two mul sub one of card add le
-- statement:
--   If `|X + X| ≤ κ * |X|` for a nonempty `X`, then `X` has Freiman dimension at most
--   `2 * κ - 1`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L245-L254
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L245-L254

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

theorem SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {κ : ℝ} {X : Finset G} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) : (freimanDim X : ℝ) ≤ 2 * κ - 1 := by sorry
