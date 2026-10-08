-- Prove2me | Theorems.Thm_WallGSL_unital_positive_map_trace_concave_nondecreasing
-- name    : WallGSL.unital_positive_map_trace_concave_nondecreasing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:59:20.176722+00:00
-- url     : https://prove2.me/theorems/decbf2b1-3afa-41d1-8850-7d859150a3ec
-- title:
--   Corollary 4 (Wall 2013): $\operatorname{tr} f(\rho)$ is nondecreasing for concave $f$
-- statement:
--   **Corollary 4 (appendix).** Let $\rho$ be an $n\times n$ density matrix and let $T$ be a positive, trace-preserving, identity-preserving linear map on $n\times n$ complex matrices. Then for every function $f$ that is **concave** on $[0,\infty)$,
--   $$\operatorname{tr} f(\rho)=\sum_{j=1}^n f(\lambda_j(\rho))\ \le\ \sum_{j=1}^n f\big(\lambda_j(T(\rho))\big)=\operatorname{tr}f\big(T(\rho)\big).$$
--   In particular the von Neumann entropy $-\operatorname{tr}(\rho\ln\rho)$ does not decrease.
--
--   This expresses that the probability eigenvalues can only evolve towards equalization; the paper uses it with the function $f(p)=0$ for $p\le p_i$ and $f(p)=p_i-p$ for $p\ge p_i$ (eqs. (A.8)–(A.10)).
--
--   **Formalization Note** The paper says "convex"; the statement is formalized for concave $f$, because the paper's own example (A.8)–(A.9) is concave and the convex version is false: for $f(p)=p^2$ and the completely depolarizing map $T(A)=\frac{\operatorname{tr}A}{n}I$, a pure state $\rho$ has $\operatorname{tr}f(\rho)=1>\frac1n=\operatorname{tr}f(T(\rho))$ when $n\ge2$.
-- source:
--   A. C. Wall, The generalized second law implies a quantum singularity theorem, Class. Quantum Grav. 30 (2013) 165003, https://doi.org/10.1088/0264-9381/30/16/165003, Appendix, Corollary 4 and eqs. (A.8)–(A.10), p. 32

import Mathlib

open Matrix
open scoped ComplexOrder

namespace WallGSL

/-- Corollary 4 (appendix) of Wall (2013), with the convexity condition read as concavity
(see the formalization note): for every function `f` concave on `[0, ∞)`, the quantity
`tr f(ρ) = ∑ⱼ f(pⱼ)` does not decrease under a trace-preserving, identity-preserving,
positive linear map `T`. -/
theorem unital_positive_map_trace_concave_nondecreasing
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hT_pos : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → (T A).PosSemidef)
    (hT_trace : ∀ A : Matrix (Fin n) (Fin n) ℂ, (T A).trace = A.trace)
    (hT_one : T 1 = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) (hρ_tr : ρ.trace = 1)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) :
    ∑ j, f (hρ.isHermitian.eigenvalues j) ≤ ∑ j, f ((hT_pos ρ hρ).isHermitian.eigenvalues j) := by sorry

end WallGSL
