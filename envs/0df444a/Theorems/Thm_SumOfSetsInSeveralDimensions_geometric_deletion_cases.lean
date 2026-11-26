-- Prove2me | Theorems.Thm_SumOfSetsInSeveralDimensions_geometric_deletion_cases
-- name    : SumOfSetsInSeveralDimensions.geometric_deletion_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:13.451674+00:00
-- url     : https://prove2.me/theorems/3221c7fd-7c9e-4096-ab08-bcbd8d587120
-- title:
--   Sum Of Sets In Several Dimensions: geometric deletion cases
-- statement:
--   **Lemma 2.1 of Ruzsa.** Let `X` and `Y` contain `0`, have at least two points each, and have
--   all other elements lexicographically positive, and let `X + Y` have affine dimension `d`. Then
--   removing `0` from `X`, from `Y` or from both gives a sumset of dimension `d` with at least `d + 1`
--   fewer points, or a sumset of dimension `d - 1` with at least `|Y|` or `|X|` fewer points, as
--   listed in the statement.
--
--   Source: https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/GeometricDeletion.lean#L331-L366
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/GeometricDeletion.lean#L331-L366

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_SumOfSetsInSeveralDimensions_GeometricDeletion
set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D d : ℕ} {X Y : Finset (Fin D → ℝ)} {x₀ y₀ : Fin D → ℝ}

theorem SumOfSetsInSeveralDimensions.geometric_deletion_cases (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x) (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hXcard : 2 ≤ #X) (hYcard : 2 ≤ #Y) (hdim : (X + Y).affineDim = d) :
    ((X.erase 0 + Y.erase 0).affineDim = d ∧
      #(X.erase 0 + Y.erase 0) + d + 1 ≤ #(X + Y)) ∨
      ((X.erase 0 + Y.erase 0).affineDim = d - 1 ∧
        #Y + #(X.erase 0 + Y.erase 0) ≤ #(X + Y)) ∨
      ((X.erase 0 + Y).affineDim = d - 1 ∧ #Y + #(X.erase 0 + Y) ≤ #(X + Y)) ∨
      ((X + Y.erase 0).affineDim = d - 1 ∧ #X + #(X + Y.erase 0) ≤ #(X + Y)) := by sorry
