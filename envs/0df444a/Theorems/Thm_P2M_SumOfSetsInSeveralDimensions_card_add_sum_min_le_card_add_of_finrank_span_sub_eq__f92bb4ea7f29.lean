-- Prove2me | Theorems.Thm_P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq__f92bb4ea7f29
-- name    : P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq__f92bb4ea7f29
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:28.376003+00:00
-- url     : https://prove2.me/theorems/6d6eb09b-4b9c-581f-92c6-8524a2544084
-- title:
--   P2 M Sum Of Sets In Several Dimensions card add sum min le card add of finrank span sub eq  f92bb4ea7f29: P2 M Sum Of Sets In Several Dimensions card add sum min le card add of finrank span sub eq  f9
-- statement:
--   **Ruzsa's theorem.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty, `|B| ≤ |A|` and `A + B` has
--   affine dimension `d`, then `|A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t) ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L30-L34
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L30-L34

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

theorem P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq__f92bb4ea7f29 {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by sorry

alias «SumOfSetsInSeveralDimensions».«card_add_sum_min_le_card_add_of_finrank_span_sub_eq'» := P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_finrank_span_sub_eq__f92bb4ea7f29
