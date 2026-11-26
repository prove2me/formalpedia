-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq
-- name    : SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:31.435752+00:00
-- url     : https://prove2.me/theorems/bc1c14d9-ebe4-4856-8201-47783f5fdfb7
-- title:
--   Sum Of Sets In Several Dimensions: card add sum min le card add of finrank span sub eq
-- statement:
--   Ruzsa's theorem, with the affine dimension of `A + B` written as the dimension of the span of
--   `(A + B) - (A + B)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean#L107-L111
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean#L107-L111

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise

theorem SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by sorry
