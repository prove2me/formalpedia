-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_max_card_add_mul_min_card_le_card_add_add
-- name    : SumOfSetsInSeveralDimensions.max_card_add_mul_min_card_le_card_add_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:23.917817+00:00
-- url     : https://prove2.me/theorems/f63c601d-ce6b-4e15-a785-e84c540b3383
-- title:
--   Sum Of Sets In Several Dimensions: max card add mul min card le card add add
-- statement:
--   The asymmetric form of Freiman's lemma without an assumption on which set is larger.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L104-L111
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L104-L111

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

theorem SumOfSetsInSeveralDimensions.max_card_add_mul_min_card_le_card_add_add (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : d ≤ (A + B).affineDim) :
    max #A #B + d * min #A #B ≤ #(A + B) + d * (d + 1) / 2 := by sorry
