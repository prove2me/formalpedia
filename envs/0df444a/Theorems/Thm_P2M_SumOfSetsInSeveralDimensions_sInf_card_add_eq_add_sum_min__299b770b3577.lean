-- Prove2me | Theorems.Thm_P2M_SumOfSetsInSeveralDimensions_sInf_card_add_eq_add_sum_min__299b770b3577
-- name    : P2M_SumOfSetsInSeveralDimensions_sInf_card_add_eq_add_sum_min__299b770b3577
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:31.237694+00:00
-- url     : https://prove2.me/theorems/a4b6b615-fa42-5e27-9558-1fbf1dae0252
-- title:
--   P2 M Sum Of Sets In Several Dimensions s Inf card add eq add sum min  299b770b3577: P2 M Sum Of Sets In Several Dimensions s Inf card add eq add sum min  299b770b3577
-- statement:
--   **Ruzsa's Theorem 2.** For `d ≥ 1`, `1 ≤ m ≤ n` and `n ≥ d + 1`, the least size of `A + B`
--   over `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `A + B` of affine dimension `d` is
--   `n + ∑ j ∈ {1, …, m - 1}, min d (n - j)`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L48-L53
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L48-L53

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

theorem P2M_SumOfSetsInSeveralDimensions_sInf_card_add_eq_add_sum_min__299b770b3577 {d m n : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin d → ℝ))) = d ∧
      #(A + B) = k} = n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) := by sorry

alias «SumOfSetsInSeveralDimensions».«sInf_card_add_eq_add_sum_min'» := P2M_SumOfSetsInSeveralDimensions_sInf_card_add_eq_add_sum_min__299b770b3577
