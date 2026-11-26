-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_card
-- name    : SumOfSetsInSeveralDimensions.normalize_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:58.195715+00:00
-- url     : https://prove2.me/theorems/2e4cb9f5-2b0a-4d04-b8d8-01d585328050
-- title:
--   Sum Of Sets In Several Dimensions: normalize card
-- statement:
--   Translation does not change the number of points.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L55-L56
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L55-L56

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

theorem SumOfSetsInSeveralDimensions.normalize_card {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : #(normalize S hS) = #S := by sorry
