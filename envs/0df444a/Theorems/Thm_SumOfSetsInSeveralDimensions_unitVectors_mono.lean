-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_unitVectors_mono
-- name    : SumOfSetsInSeveralDimensions.unitVectors_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:50.08548+00:00
-- url     : https://prove2.me/theorems/63520e25-5c54-576e-ba69-5c4ff29e71e2
-- title:
--   Sum Of Sets In Several Dimensions: unit Vectors mono
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the unit Vectors mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L94-L98
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L94-L98

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

theorem SumOfSetsInSeveralDimensions.unitVectors_mono {c c' : ℕ} (hcc' : c ≤ c') : unitVectors e c ⊆ unitVectors e c' := by sorry
