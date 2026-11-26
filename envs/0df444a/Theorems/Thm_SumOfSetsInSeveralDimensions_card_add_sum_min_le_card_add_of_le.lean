-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_le
-- name    : SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:18.718018+00:00
-- url     : https://prove2.me/theorems/56a33b08-79ec-5cb1-bda2-78f009213172
-- title:
--   Sum Of Sets In Several Dimensions: card add sum min le card add of le
-- statement:
--   Ruzsa's theorem for every `d` at most the affine dimension of `A + B`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean#L99-L103
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean#L99-L103

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

theorem SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_le {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hd : d ≤ (A + B).affineDim) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by sorry
