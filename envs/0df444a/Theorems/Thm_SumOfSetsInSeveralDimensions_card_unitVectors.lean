-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_unitVectors
-- name    : SumOfSetsInSeveralDimensions.card_unitVectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:55.966891+00:00
-- url     : https://prove2.me/theorems/aab914b5-2493-4dcb-aee6-e0e09ca64dcc
-- title:
--   Sum Of Sets In Several Dimensions: card unit Vectors
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the card unit Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L73-L76
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L73-L76

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

theorem SumOfSetsInSeveralDimensions.card_unitVectors {c : ℕ} (hc : c ≤ e) : #(unitVectors e c) = c := by sorry
