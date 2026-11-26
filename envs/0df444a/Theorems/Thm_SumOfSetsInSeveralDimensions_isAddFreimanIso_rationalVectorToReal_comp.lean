-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_isAddFreimanIso_rationalVectorToReal_comp
-- name    : SumOfSetsInSeveralDimensions.isAddFreimanIso_rationalVectorToReal_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:37.751587+00:00
-- url     : https://prove2.me/theorems/8d4e36d9-e4ce-5327-98e2-85ec30cb8727
-- title:
--   Sum Of Sets In Several Dimensions: is Add Freiman Iso rational Vector To Real comp
-- statement:
--   A Freiman isomorphism into `ℚ^d` followed by the inclusion of `ℚ^d` into `ℝ^d` is a Freiman
--   isomorphism into `ℝ^d`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L61-L72
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L61-L72

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

theorem SumOfSetsInSeveralDimensions.isAddFreimanIso_rationalVectorToReal_comp {G : Type*} [AddCommMonoid G] {d : ℕ}
    {X : Finset G} {f : G → (Fin d → ℚ)}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin d → ℚ)) f) :
    IsAddFreimanIso 2 (X : Set G) (X.image (rationalVectorToReal ∘ f) : Set (Fin d → ℝ))
      (rationalVectorToReal ∘ f) := by sorry
