-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add
-- name    : SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:46.808427+00:00
-- url     : https://prove2.me/theorems/0dd0d0d9-45b2-4877-ad0a-fc59cc7060aa
-- title:
--   Sum Of Sets In Several Dimensions: card add mul card le card add add
-- statement:
--   **The asymmetric form of Freiman's lemma.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty,
--   `|B| ≤ |A|` and `A + B` has affine dimension at least `d`, then
--   `|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L81-L84
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/ClosedForm.lean#L81-L84

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

theorem SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ (A + B).affineDim) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 := by sorry
