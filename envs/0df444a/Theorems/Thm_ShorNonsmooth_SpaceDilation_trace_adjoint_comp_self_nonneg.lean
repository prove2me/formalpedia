-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_trace_adjoint_comp_self_nonneg
-- name    : ShorNonsmooth.SpaceDilation.trace_adjoint_comp_self_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:12:06.827056+00:00
-- url     : https://prove2.me/theorems/d84bf298-5e27-445c-9f4e-6d61eedeadaa
-- title:
--   Trace of A^* A is nonnegative
-- statement:
--   For a linear operator $A$ on $E_n$, $\mathrm{tr}(A^*A) \ge 0$: the trace is a sum of squared norms over any orthonormal basis.
-- source:
--   Standard trace positivity for A^*A over real inner-product spaces, isolating the nonnegativity step in the proof of Theorem 3.1 of Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 53.

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- For an operator on a finite-dimensional real inner-product space, `tr (A^* A) ≥ 0`, since the trace is the sum of the squared norms `‖A e_i‖^2` over any orthonormal basis. Needed in Theorem 3.1 to raise the trace upper bound to the power `n - 1`. -/
theorem trace_adjoint_comp_self_nonneg {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    0 ≤ LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) ((LinearMap.adjoint A).comp A) := by sorry

end ShorNonsmooth.SpaceDilation
