-- Prove2me | Theorems.Thm_P2M_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min__6f7a558aacae
-- name    : P2M_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min__6f7a558aacae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:35.377131+00:00
-- url     : https://prove2.me/theorems/bb4f268c-4a99-452b-b122-d8d0c9ec507d
-- title:
--   P2 M Sum Of Sets In Several Dimensions s Inf card add of finrank span sub right eq add sum min  6f7a558aacae: P2 M Sum Of Sets In Several Dimensions s Inf card add of finrank span sub right eq add sum
-- statement:
--   **Ruzsa's Theorem 2, with `B` of full dimension.** For `d ≥ 1`, `1 ≤ m ≤ n` and `n ≥ d + 1`,
--   the least size of `A + B` over `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `B` of affine dimension
--   `d` is `n + ∑ j ∈ {1, …, m - 1}, min d (n - j)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L58-L63
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L58-L63

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions

theorem P2M_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min__6f7a558aacae {d m n : ℕ} (hd : 1 ≤ d)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑B - ↑B : Set (Fin d → ℝ))) = d ∧ #(A + B) = k} =
      n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) := by sorry

alias «SumOfSetsInSeveralDimensions».«sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min'» := P2M_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min__6f7a558aacae
