-- Prove2me | Theorems.Thm_TraceEstimation_Hutchinson_spectral_error_bound
-- name    : TraceEstimation.Hutchinson.spectral_error_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:30:09.819862+00:00
-- url     : https://prove2.me/theorems/6c5c24cf-be55-4c1e-982b-f47fd7668915
-- title:
--   Proof of Theorem 7.1, p. 8:11 — per-direction accuracy implies $|H_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A)$
-- statement:
--   Let $A = U\Lambda U^T$ be an $n \times n$ real matrix given with an eigendecomposition: $U$ orthogonal ($U^TU = I$) and $\Lambda = \mathrm{diag}(\lambda_1, \ldots, \lambda_n)$ with every $\lambda_j \ge 0$. Fix $M \ge 1$, $\epsilon > 0$ and vectors $z_1, \ldots, z_M \in \mathbb{R}^n$; put $y_i = U^T z_i$ and let $y_{ij}$ be its $j$-th entry. If
--
--   $$\left|\frac{1}{M}\sum_{i=1}^{M} y_{ij}^2 - 1\right| \le \epsilon \quad \text{for every } j \text{ with } \lambda_j \ne 0,$$
--
--   then Hutchinson's estimator $H_M = \frac1M\sum_{i=1}^M z_i^TAz_i$ satisfies
--
--   $$|H_M - \mathrm{trace}(A)| \le \epsilon\,\mathrm{trace}(A).$$
--
--   This is the deterministic half of the proof of Theorem 7.1: it turns a bound on each eigen-direction into a relative error bound on the trace estimate. No probability is involved.
--
--   **Formalization Note** The page writes $\Lambda = UAU^T$ together with $y_i = U^Tz_i$; these fit together only for $A = U\Lambda U^T$, which is the convention stated here. The eigenvalues are indexed by all $j$ and the hypothesis is required only for $\lambda_j \ne 0$, which is the page's range $j = 1, \ldots, \mathrm{rank}(A)$ after its reordering. Nonnegativity of the $\lambda_j$ (positive semi-definiteness) is a hypothesis, as in the page's "A is symmetric and semidefinite".
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:11, Section 7, proof of Theorem 7.1, last display

import Mathlib
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- Proof of Theorem 7.1 (Avron–Toledo, p. 8:11, last display), a deterministic step.
Let `A = U Λ Uᵀ` with `U` orthogonal and `Λ = diag(λ_1, …, λ_n)`, `λ_j ≥ 0` (the
eigendecomposition of a symmetric positive semi-definite `A`). Fix `M ≥ 1`, `ε > 0` and
vectors `z_1, …, z_M ∈ ℝⁿ`, and put `y_i = Uᵀ z_i` with entries `y_ij`. If
`|(1/M) ∑_{i=1}^M y_ij² - 1| ≤ ε` for every `j` with `λ_j ≠ 0`, then
`|H_M - trace(A)| ≤ ε · trace(A)`, where `H_M = (1/M) ∑_i z_iᵀ A z_i`.
The page writes `Λ = U A Uᵀ` and `y_i = Uᵀ z_i`; these are consistent only for
`A = U Λ Uᵀ`, the convention used here. -/
theorem spectral_error_bound {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) (lam : Fin n → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hA : A = U * diagonal lam * Uᵀ) (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (ω : Fin M → Fin n → ℝ)
    (hω : ∀ j, lam j ≠ 0 → |(M : ℝ)⁻¹ * ∑ i : Fin M, (Uᵀ *ᵥ ω i) j ^ 2 - 1| ≤ ε) :
    |hutchinsonEstimator A M ω - A.trace| ≤ ε * A.trace := by sorry

end TraceEstimation.Hutchinson
