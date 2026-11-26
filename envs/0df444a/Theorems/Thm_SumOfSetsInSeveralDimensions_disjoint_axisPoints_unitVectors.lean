-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_disjoint_axisPoints_unitVectors
-- name    : SumOfSetsInSeveralDimensions.disjoint_axisPoints_unitVectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:36.239808+00:00
-- url     : https://prove2.me/theorems/5b81f59e-24e5-5458-a910-3a1f3b73f359
-- title:
--   Sum Of Sets In Several Dimensions: disjoint axis Points unit Vectors
-- statement:
--   The Sum Of Sets In Several Dimensions construction uses the disjoint axis Points unit Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L78-L84
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L78-L84

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

theorem SumOfSetsInSeveralDimensions.disjoint_axisPoints_unitVectors (k c : ℕ) :
    Disjoint (axisPoints e k) (unitVectors e c) := by sorry
