-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_exists_card_add_le_sumsetCardLowerBound
-- name    : SumOfSetsInSeveralDimensions.exists_card_add_le_sumsetCardLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:02.792829+00:00
-- url     : https://prove2.me/theorems/1196c7e2-3794-4629-8194-0a165d0ddd18
-- title:
--   Sum Of Sets In Several Dimensions: exists card add le sumset Card Lower Bound
-- statement:
--   For `1 ≤ m ≤ n` and `e + 2 ≤ n`, there are `A, B ⊆ ℝ^(e + 1)` with `|A| = m`, `|B| = n`, `B`
--   of affine dimension `e + 1` and `|A + B| ≤ G_(e + 1)(m, n)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L214-L220
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L214-L220

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

theorem SumOfSetsInSeveralDimensions.exists_card_add_le_sumsetCardLowerBound {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : e + 2 ≤ n) :
    ∃ A B : Finset (Fin (e + 1) → ℝ), #A = m ∧ #B = n ∧ B.affineDim = e + 1 ∧
      #(A + B) ≤ sumsetCardLowerBound (e + 1) m n := by sorry
