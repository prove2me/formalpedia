-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso
-- name    : SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:49.257694+00:00
-- url     : https://prove2.me/theorems/1ec1be1c-f037-4eba-9def-bdbcfe8cfdd7
-- title:
--   Sum Of Sets In Several Dimensions: le two mul sub one of is Add Freiman Iso
-- statement:
--   If `|X + X| ≤ κ * |X|` for a nonempty `X` and `f` is a Freiman isomorphism of order `2` from
--   `X` onto a subset of `ℝ^r` of affine dimension `r`, then `r ≤ 2 * κ - 1`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L175-L187
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L175-L187

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

theorem SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : (X.image f).affineDim = r) : (r : ℝ) ≤ 2 * κ - 1 := by sorry
