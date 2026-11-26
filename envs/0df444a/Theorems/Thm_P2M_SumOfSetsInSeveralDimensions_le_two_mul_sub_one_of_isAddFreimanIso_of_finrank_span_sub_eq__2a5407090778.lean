-- Prove2me | Theorems.Thm_P2M_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq__2a5407090778
-- name    : P2M_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq__2a5407090778
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:56.285098+00:00
-- url     : https://prove2.me/theorems/5c049c4b-3640-4076-88cd-3150ed3f72c2
-- title:
--   P2 M Sum Of Sets In Several Dimensions le two mul sub one of is Add Freiman Iso of finrank span sub eq  2a5407090778: P2 M Sum Of Sets In Several Dimensions le two mul sub one of is Add Freiman Iso of
-- statement:
--   **The bound on the Freiman dimension.** If `X` is a nonempty finite subset of a cancellative
--   commutative monoid with `|X + X| ≤ κ * |X|` for a real `κ`, and `f` is a Freiman isomorphism of
--   order `2` from `X` onto a subset of `ℝ^r` of affine dimension `r`, then `r ≤ 2 * κ - 1`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L81-L88
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L81-L88

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions

theorem P2M_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq__2a5407090778 {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    (r : ℝ) ≤ 2 * κ - 1 := by sorry

alias «SumOfSetsInSeveralDimensions».«le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq'» := P2M_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq__2a5407090778
