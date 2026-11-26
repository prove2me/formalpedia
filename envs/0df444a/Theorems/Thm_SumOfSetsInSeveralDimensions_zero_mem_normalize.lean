-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_zero_mem_normalize
-- name    : SumOfSetsInSeveralDimensions.zero_mem_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:47.80027+00:00
-- url     : https://prove2.me/theorems/3cdaf595-4128-595d-b446-32c8c263e6f6
-- title:
--   Sum Of Sets In Several Dimensions: zero mem normalize
-- statement:
--   The translated set contains the origin.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L59-L60
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean#L59-L60

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

theorem SumOfSetsInSeveralDimensions.zero_mem_normalize {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : 0 ∈ normalize S hS := by sorry
