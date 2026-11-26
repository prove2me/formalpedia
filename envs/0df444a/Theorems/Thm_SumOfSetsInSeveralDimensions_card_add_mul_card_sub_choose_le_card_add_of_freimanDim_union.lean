-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union
-- name    : SumOfSetsInSeveralDimensions.card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:08.154579+00:00
-- url     : https://prove2.me/theorems/b71fc3ab-a26e-44ce-9fb8-84f5dd248cef
-- title:
--   Sum Of Sets In Several Dimensions: card add mul card sub choose le card add of freiman Dim union
-- statement:
--   Let `A` and `B` be finite with `B` nonempty and `|B| ≤ |A|`, and let `r ≥ 1` be the Freiman
--   dimension of `A ∪ B`. Then `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L236-L241
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L236-L241

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

theorem SumOfSetsInSeveralDimensions.card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union
    {G : Type*} [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} (hr : 1 ≤ r)
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : freimanDim (A ∪ B) = r) :
    #A + (r - 1) * #B - (r + 1).choose 2 ≤ #(A + B) := by sorry
