-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq
-- name    : SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:19.127929+00:00
-- url     : https://prove2.me/theorems/ad9efc0e-c912-5533-b795-2fb757e91dfc
-- title:
--   Sum Of Sets In Several Dimensions: card add sum min le card add of is Add Freiman Iso of finrank span sub eq
-- statement:
--   Ruzsa's theorem for a Freiman model, with the affine dimension of the model written as the
--   dimension of the span of its differences.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L124-L132
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L124-L132

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

theorem SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*}
    [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ}
    (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (↑((A ∪ B).image f) - ↑((A ∪ B).image f) : Set (Fin r → ℝ))) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by sorry
