-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_axisPoints
-- name    : SumOfSetsInSeveralDimensions.card_axisPoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:51.581804+00:00
-- url     : https://prove2.me/theorems/7442cd65-ffe9-4444-9d60-0a5e06c6cecf
-- title:
--   Sum Of Sets In Several Dimensions: card axis Points
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the card axis Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L68-L71
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L68-L71

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Definitions.Def_SumOfSetsInSeveralDimensions_Construction
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}

theorem SumOfSetsInSeveralDimensions.card_axisPoints (e k : ℕ) : #(axisPoints e k) = k + 1 := by sorry
