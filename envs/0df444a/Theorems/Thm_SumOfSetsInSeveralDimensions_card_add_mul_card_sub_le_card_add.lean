-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_mul_card_sub_le_card_add
-- name    : SumOfSetsInSeveralDimensions.card_add_mul_card_sub_le_card_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:27.282128+00:00
-- url     : https://prove2.me/theorems/b99e7774-10e7-4bef-ab6e-a5891289f672
-- title:
--   Sum Of Sets In Several Dimensions: card add mul card sub le card add
-- statement:
--   The asymmetric form of Freiman's lemma in `ℝ`: `|A| + d * |B| - d * (d + 1) / 2 ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L96-L101
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L96-L101

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

theorem SumOfSetsInSeveralDimensions.card_add_mul_card_sub_le_card_add (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) :
    (#A : ℝ) + d * #B - d * (d + 1) / 2 ≤ #(A + B) := by sorry
