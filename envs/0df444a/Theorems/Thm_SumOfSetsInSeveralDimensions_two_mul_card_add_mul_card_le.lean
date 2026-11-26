-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_two_mul_card_add_mul_card_le
-- name    : SumOfSetsInSeveralDimensions.two_mul_card_add_mul_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:46.780354+00:00
-- url     : https://prove2.me/theorems/f26b0a60-7a55-4d65-86dd-2ad4fa77149b
-- title:
--   Sum Of Sets In Several Dimensions: two mul card add mul card le
-- statement:
--   The closed form of Ruzsa's bound, multiplied by two: `2 * (|A| + d * |B|)` is at most
--   `2 * |A + B| + d * (d + 1)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L73-L76
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L73-L76

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

theorem SumOfSetsInSeveralDimensions.two_mul_card_add_mul_card_le (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) : 2 * (#A + d * #B) ≤ 2 * #(A + B) + d * (d + 1) := by sorry
