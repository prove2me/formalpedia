-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_image_eq_of_kernel_iff
-- name    : SumOfSetsInSeveralDimensions.card_image_eq_of_kernel_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:31.501122+00:00
-- url     : https://prove2.me/theorems/06ed8244-8e65-4aab-8eda-640fcab38816
-- title:
--   Sum Of Sets In Several Dimensions: card image eq of kernel iff
-- statement:
--   Two maps with the same fibres on `s` have images of `s` of the same size.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L75-L89
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L75-L89

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

theorem SumOfSetsInSeveralDimensions.card_image_eq_of_kernel_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {s : Finset α} {f : α → β} {g : α → γ}
    (h : ∀ x ∈ s, ∀ y ∈ s, (f x = f y ↔ g x = g y)) :
    #(s.image f) = #(s.image g) := by sorry
