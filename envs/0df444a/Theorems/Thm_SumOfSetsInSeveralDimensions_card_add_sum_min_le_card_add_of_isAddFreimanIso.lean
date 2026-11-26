-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso
-- name    : SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:36.453496+00:00
-- url     : https://prove2.me/theorems/8a6849b2-1583-415f-88a1-038138f41239
-- title:
--   Sum Of Sets In Several Dimensions: card add sum min le card add of is Add Freiman Iso
-- statement:
--   **Ruzsa's theorem for a Freiman model.** Let `A` and `B` be finite subsets of a commutative
--   monoid with `B` nonempty and `|B| ≤ |A|`, and let `f` be a Freiman isomorphism of order `2` from
--   `A ∪ B` onto a subset of `ℝ^r` of affine dimension `r`. Then
--   `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L107-L120
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L107-L120

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

theorem SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ} (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : ((A ∪ B).image f).affineDim = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by sorry
