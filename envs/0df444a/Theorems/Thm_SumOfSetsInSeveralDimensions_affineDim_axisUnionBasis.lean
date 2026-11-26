-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_affineDim_axisUnionBasis
-- name    : SumOfSetsInSeveralDimensions.affineDim_axisUnionBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:58.348606+00:00
-- url     : https://prove2.me/theorems/afad22a6-2900-5267-9bf7-8d709f78dafc
-- title:
--   Sum Of Sets In Several Dimensions: affine Dim axis Union Basis
-- statement:
--   The set `axisUnionBasis e k e` contains `0`, `e₀` and all of `e₁, …, e_e`, so it has affine
--   dimension `e + 1` when `k ≥ 1`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L111-L125
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L111-L125

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

theorem SumOfSetsInSeveralDimensions.affineDim_axisUnionBasis {k : ℕ} (hk : 1 ≤ k) :
    (axisUnionBasis e k e).affineDim = e + 1 := by sorry
