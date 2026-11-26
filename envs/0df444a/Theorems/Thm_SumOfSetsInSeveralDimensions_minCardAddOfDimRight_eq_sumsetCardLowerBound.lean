-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_minCardAddOfDimRight_eq_sumsetCardLowerBound
-- name    : SumOfSetsInSeveralDimensions.minCardAddOfDimRight_eq_sumsetCardLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:16.731803+00:00
-- url     : https://prove2.me/theorems/04d5ed9e-a55c-4e92-9f63-31e7a6a91d13
-- title:
--   Sum Of Sets In Several Dimensions: min Card Add Of Dim Right eq sumset Card Lower Bound
-- statement:
--   **Theorem 2 of Ruzsa, for `F'_d`.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`,
--   `F'_d(m, n) = G_d(m, n)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/MinCardAdd.lean#L82-L90
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/MinCardAdd.lean#L82-L90

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_Construction
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {d m n : ℕ}

theorem SumOfSetsInSeveralDimensions.minCardAddOfDimRight_eq_sumsetCardLowerBound (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) : minCardAddOfDimRight d m n = sumsetCardLowerBound d m n := by sorry
