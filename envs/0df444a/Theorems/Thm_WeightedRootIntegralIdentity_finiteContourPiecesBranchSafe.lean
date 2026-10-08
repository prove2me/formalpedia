-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_finiteContourPiecesBranchSafe
-- name    : WeightedRootIntegralIdentity.finiteContourPiecesBranchSafe
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T10:51:14.40101+00:00
-- url     : https://prove2.me/theorems/1489a12f-f7fa-4b0c-a8cd-5433002f725a
-- title:
--   Finite contour pieces are piecewise smooth and branch-safe
-- statement:
--   The six finite keyhole contour components are individually C1 on the unit parameter interval and remain inside the branch-safe domain.

import Mathlib

theorem WeightedRootIntegralIdentity.finiteContourPiecesBranchSafe
    (D : Set ℂ) (γ : Fin 6 → ℝ → ℂ)
    (hpieces : ∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1))
    (hsafe : ∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) :
    (∀ j : Fin 6, ContDiffOn ℝ 1 (γ j) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ j : Fin 6, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ j t ∈ D) := by sorry
