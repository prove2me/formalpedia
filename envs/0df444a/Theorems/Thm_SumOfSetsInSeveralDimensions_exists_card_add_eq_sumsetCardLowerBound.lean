-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_exists_card_add_eq_sumsetCardLowerBound
-- name    : SumOfSetsInSeveralDimensions.exists_card_add_eq_sumsetCardLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:50.490642+00:00
-- url     : https://prove2.me/theorems/7e1fb747-592e-522c-9231-8ff1243db8a7
-- title:
--   Sum Of Sets In Several Dimensions: exists card add eq sumset Card Lower Bound
-- statement:
--   **The sets of Section 3.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`, there are `A, B ⊆ ℝ^d`
--   with `|A| = m`, `|B| = n`, `B` of affine dimension `d` and
--   `|A + B| = n + ∑ j ∈ {1, …, m - 1}, min d (n - j)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L225-L235
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Construction.lean#L225-L235

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

theorem SumOfSetsInSeveralDimensions.exists_card_add_eq_sumsetCardLowerBound {d m n : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ B.affineDim = d ∧
      #(A + B) = sumsetCardLowerBound d m n := by sorry
