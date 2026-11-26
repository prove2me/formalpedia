-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add
-- name    : SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:06:18.821101+00:00
-- url     : https://prove2.me/theorems/65f11a61-e9d9-47a2-b51e-3d007273f5a2
-- title:
--   Sum Of Sets In Several Dimensions: card add sum min le card add
-- statement:
--   **Ruzsa's theorem.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty, `|B| ≤ |A|` and `A + B` has
--   affine dimension `d`, then `|A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t) ≤ |A + B|`.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean#L92-L96
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/LowerBound.lean#L92-L96

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise

theorem SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add {D d : ℕ} {A B : Finset (Fin D → ℝ)}
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : (A + B).affineDim = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by sorry
