-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_axisUnionBasis
-- name    : SumOfSetsInSeveralDimensions.card_axisUnionBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:43.273975+00:00
-- url     : https://prove2.me/theorems/623cf012-0948-4724-9375-4cb1d01ec228
-- title:
--   Sum Of Sets In Several Dimensions: card axis Union Basis
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the card axis Union Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L86-L88
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L86-L88

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

theorem SumOfSetsInSeveralDimensions.card_axisUnionBasis (k : ℕ) {c : ℕ} (hc : c ≤ e) : #(axisUnionBasis e k c) = k + 1 + c := by sorry
