-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_image_of_isAddFreimanIso
-- name    : SumOfSetsInSeveralDimensions.card_add_image_of_isAddFreimanIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:23.001141+00:00
-- url     : https://prove2.me/theorems/ae899547-06fa-4bb6-8064-433afe54f7de
-- title:
--   Sum Of Sets In Several Dimensions: card add image of is Add Freiman Iso
-- statement:
--   A Freiman isomorphism of order `2` on `X` preserves the size of `A + B` for `A, B ⊆ X`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L92-L101
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L92-L101

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

theorem SumOfSetsInSeveralDimensions.card_add_image_of_isAddFreimanIso {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H] {X A B : Finset G} {f : G → H}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set H) f) (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #(A.image f + B.image f) = #(A + B) := by sorry
