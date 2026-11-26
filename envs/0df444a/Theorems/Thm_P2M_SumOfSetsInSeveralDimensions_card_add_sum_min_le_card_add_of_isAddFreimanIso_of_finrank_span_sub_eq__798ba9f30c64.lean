-- Prove2me | Theorems.Thm_P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq__798ba9f30c64
-- name    : P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq__798ba9f30c64
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:10:45.920155+00:00
-- url     : https://prove2.me/theorems/8d3d9aca-6684-4eb2-92e0-9c0db4bf2060
-- title:
--   P2 M Sum Of Sets In Several Dimensions card add sum min le card add of is Add Freiman Iso of finrank span sub eq  798ba9f30c64: P2 M Sum Of Sets In Several Dimensions card add sum min le card add of i
-- statement:
--   **Ruzsa's theorem for a Freiman model.** If `A` and `B` are finite subsets of a commutative
--   monoid, `B` is nonempty, `|B| ≤ |A|` and `f` is a Freiman isomorphism of order `2` from `A ∪ B` onto
--   a subset of `ℝ^r` of affine dimension `r`, then
--   `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L69-L76
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/Solution.lean#L69-L76

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

theorem P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq__798ba9f30c64 {G : Type*}
    [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ}
    (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (↑((A ∪ B).image f) - ↑((A ∪ B).image f) : Set (Fin r → ℝ))) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by sorry

alias «SumOfSetsInSeveralDimensions».«card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq'» := P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq__798ba9f30c64
