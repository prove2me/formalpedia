-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_rationalVectorToReal_injective
-- name    : SumOfSetsInSeveralDimensions.rationalVectorToReal_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:14.740384+00:00
-- url     : https://prove2.me/theorems/25b02d41-b0fe-5353-9552-773c09f42d22
-- title:
--   Sum Of Sets In Several Dimensions: rational Vector To Real injective
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the rational Vector To Real injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L50-L52
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimensionSumsetBounds.lean#L50-L52

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

theorem SumOfSetsInSeveralDimensions.rationalVectorToReal_injective {d : ℕ} :
    Function.Injective (rationalVectorToReal (d := d)) := by sorry
