-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq
-- name    : SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:23.077887+00:00
-- url     : https://prove2.me/theorems/de587ae3-a53a-5e57-bc14-6c444f2ffced
-- title:
--   Sum Of Sets In Several Dimensions: le two mul sub one of is Add Freiman Iso of finrank span sub eq
-- statement:
--   The bound `r ≤ 2 * κ - 1` for a Freiman model, with the affine dimension of the model written
--   as the dimension of the span of its differences.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L191-L199
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L191-L199

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

theorem SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    (r : ℝ) ≤ 2 * κ - 1 := by sorry
