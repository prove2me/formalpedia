-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_det_adjoint_comp_self
-- name    : ShorNonsmooth.SpaceDilation.det_adjoint_comp_self
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:59.480081+00:00
-- url     : https://prove2.me/theorems/1488464a-3169-4188-aebf-e9a6d297e439
-- title:
--   Determinant of A^* A is the square of the determinant
-- statement:
--   For a linear operator $A$ on $E_n$, $\det(A^*A) = (\det A)^2$. Over $\mathbb{R}$ the adjoint has the same determinant as the operator, and the determinant is multiplicative.
-- source:
--   Standard determinant identities for adjoints over real inner-product spaces, isolating the determinant-squaring step in the proof of Theorem 3.1 of Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 53.

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- For an operator on a finite-dimensional real inner-product space, `det (A^* A) = (det A)^2`, since `det (A^*) = det A` over `ℝ`. Used with the accumulated-determinant identity to get `det (A_k^* A_k) = (∏ α_j)^2 (det A_0)^2` in Theorem 3.1. -/
theorem det_adjoint_comp_self {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LinearMap.det ((LinearMap.adjoint A).comp A) = (LinearMap.det A) ^ 2 := by sorry

end ShorNonsmooth.SpaceDilation
