-- Prove2me | Theorems.Thm_P2M_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub__e0ebb9409f0f
-- name    : P2M_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub__e0ebb9409f0f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:26.054994+00:00
-- url     : https://prove2.me/theorems/9263cec5-9e5c-52cf-8801-57c4bef3a294
-- title:
--   P2 M Sum Of Sets In Several Dimensions card add mul card le card add add of le finrank span sub  e0ebb9409f0f: P2 M Sum Of Sets In Several Dimensions card add mul card le card add add of le finrank sp
-- statement:
--   **The asymmetric form of Freiman's lemma.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty,
--   `|B| ≤ |A|` and `A + B` has affine dimension at least `d`, then
--   `|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L39-L43
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L39-L43

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

theorem P2M_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub__e0ebb9409f0f {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ)))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 := by sorry

alias «SumOfSetsInSeveralDimensions».«card_add_mul_card_le_card_add_add_of_le_finrank_span_sub'» := P2M_SumOfSetsInSeveralDimensions_card_add_mul_card_le_card_add_add_of_le_finrank_span_sub__e0ebb9409f0f
