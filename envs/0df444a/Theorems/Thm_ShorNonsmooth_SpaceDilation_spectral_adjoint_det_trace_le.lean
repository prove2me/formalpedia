-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_spectral_adjoint_det_trace_le
-- name    : ShorNonsmooth.SpaceDilation.spectral_adjoint_det_trace_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:11:21.975021+00:00
-- url     : https://prove2.me/theorems/3f47664f-32ef-4ffa-b214-b5383699ef9c
-- title:
--   Adjoint-norm determinant-trace estimate for a left-invertible operator
-- statement:
--   Let $A, B$ be operators on $E_n$ with $BA = I$ and let $S = A^*A$. Then $\|B^*g\|^2 \det S \le \|g\|^2 (\mathrm{tr}\,S)^{n-1}$ for every $g$. This is $BB^* = S^{-1}$ combined with $\det S \le \lambda_{\min}(S)(\mathrm{tr}\,S)^{n-1}$ for the positive-semidefinite operator $S$.
-- source:
--   Spectral determinant-trace comparison for positive-semidefinite operators, isolating the eigenvalue step in the proof of Theorem 3.1 of Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 53.

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- Spectral estimate for the proof of Theorem 3.1: if `B ∘ A = id` then `B B^* = (A^* A)^{-1}`, so `‖B^* g‖^2 ≤ ‖g‖^2 / λ_min(A^* A)` with `λ_min(A^* A) ≥ det(A^* A) / tr(A^* A)^{n-1}`, since each eigenvalue of the positive-semidefinite `A^* A` lies between `0` and the trace. -/
theorem spectral_adjoint_det_trace_le {n : ℕ} (hn : 0 < n)
    (A B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hBA : B.comp A = LinearMap.id)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖(LinearMap.adjoint B) g‖ ^ 2 *
        LinearMap.det (LinearMap.adjoint A |>.comp A) ≤
      ‖g‖ ^ 2 *
        (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (LinearMap.adjoint A |>.comp A)) ^ (n - 1) := by sorry

end ShorNonsmooth.SpaceDilation
