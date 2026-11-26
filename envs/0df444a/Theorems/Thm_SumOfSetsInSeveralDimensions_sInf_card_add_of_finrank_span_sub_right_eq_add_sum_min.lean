-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min
-- name    : SumOfSetsInSeveralDimensions.sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:24.451163+00:00
-- url     : https://prove2.me/theorems/3a187228-89f5-4b1d-9443-a162d326d69a
-- title:
--   Sum Of Sets In Several Dimensions: s Inf card add of finrank span sub right eq add sum min
-- statement:
--   Theorem 2 of Ruzsa for `F'_d`, with `F'_d` and `G_d` unfolded and the affine dimension of `B`
--   written as the dimension of the span of `B - B`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/MinCardAdd.lean#L103-L109
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/MinCardAdd.lean#L103-L109

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

theorem SumOfSetsInSeveralDimensions.sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑B - ↑B : Set (Fin d → ℝ))) = d ∧ #(A + B) = k} =
      n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) := by sorry
