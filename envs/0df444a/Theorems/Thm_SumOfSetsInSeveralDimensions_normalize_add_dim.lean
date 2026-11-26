-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_add_dim
-- name    : SumOfSetsInSeveralDimensions.normalize_add_dim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:07.143822+00:00
-- url     : https://prove2.me/theorems/d894fea2-da31-5e1f-9a15-46b7c55f5aef
-- title:
--   Sum Of Sets In Several Dimensions: normalize add dim
-- statement:
--   The sum of the translates of `A` and `B` has the affine dimension of `A + B`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L93-L95
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L93-L95

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}

theorem SumOfSetsInSeveralDimensions.normalize_add_dim {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    (normalize A hA + normalize B hB).affineDim = (A + B).affineDim := by sorry
