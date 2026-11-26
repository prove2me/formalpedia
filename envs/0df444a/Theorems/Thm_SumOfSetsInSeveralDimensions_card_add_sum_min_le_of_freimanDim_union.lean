-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_of_freimanDim_union
-- name    : SumOfSetsInSeveralDimensions.card_add_sum_min_le_of_freimanDim_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:32.69835+00:00
-- url     : https://prove2.me/theorems/3f122fc2-b070-55b8-9fcf-5ca5f793335a
-- title:
--   Sum Of Sets In Several Dimensions: card add sum min le of freiman Dim union
-- statement:
--   Let `A` and `B` be finite with `B` nonempty and `|B| ≤ |A|`, and let `r ≥ 1` be the Freiman
--   dimension of `A ∪ B`. Then `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L225-L232
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L225-L232

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

theorem SumOfSetsInSeveralDimensions.card_add_sum_min_le_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {A B : Finset G} (hr : 1 ≤ r) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : freimanDim (A ∪ B) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by sorry
