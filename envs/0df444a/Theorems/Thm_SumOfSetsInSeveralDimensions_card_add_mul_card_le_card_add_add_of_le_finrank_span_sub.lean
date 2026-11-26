-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub
-- name    : SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:38.32766+00:00
-- url     : https://prove2.me/theorems/7e207b91-7fe1-463e-a752-b40c3b4ee475
-- title:
--   Sum Of Sets In Several Dimensions: card add mul card le card add add of le finrank span sub
-- statement:
--   The asymmetric form of Freiman's lemma, with the affine dimension of `A + B` written as the
--   dimension of the span of `(A + B) - (A + B)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L88-L93
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L88-L93

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {A B : Finset (Fin D → ℝ)}

theorem SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ)))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 := by sorry
