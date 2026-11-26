-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_axisPoints_mono
-- name    : SumOfSetsInSeveralDimensions.axisPoints_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:54.406493+00:00
-- url     : https://prove2.me/theorems/cd99addf-f1a4-46d0-8ee1-028fe64957db
-- title:
--   Sum Of Sets In Several Dimensions: axis Points mono
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the axis Points mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L90-L92
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L90-L92

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

theorem SumOfSetsInSeveralDimensions.axisPoints_mono {k l : ℕ} (hkl : k ≤ l) : axisPoints e k ⊆ axisPoints e l := by sorry
