-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_normalize_add_card
-- name    : SumOfSetsInSeveralDimensions.normalize_add_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:04.486904+00:00
-- url     : https://prove2.me/theorems/69527768-e85b-5d25-89a6-8c8c5bf4c503
-- title:
--   Sum Of Sets In Several Dimensions: normalize add card
-- statement:
--   The sum of the translates of `A` and `B` has as many points as `A + B`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L87-L90
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L87-L90

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

theorem SumOfSetsInSeveralDimensions.normalize_add_card {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    #(normalize A hA + normalize B hB) = #(A + B) := by sorry
