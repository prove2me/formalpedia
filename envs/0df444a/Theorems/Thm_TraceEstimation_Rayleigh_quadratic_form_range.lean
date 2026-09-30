-- Prove2me | Theorems.Thm_TraceEstimation_Rayleigh_quadratic_form_range
-- name    : TraceEstimation.Rayleigh.quadratic_form_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:21:35.285159+00:00
-- url     : https://prove2.me/theorems/e1d1c698-0373-4958-90be-76a7b7da9c3d
-- title:
--   Theorem 6.1, proof — $0 \le z^TAz \le n\lambda_n \le \frac{n}{\mathrm{rank}(A)}\mathrm{trace}(A)\kappa_f(A)$ when $z^Tz = n$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a nonzero symmetric positive semi-definite matrix with largest eigenvalue $\lambda_n$, and let $\kappa_f(A)$ be the ratio between its largest and smallest nonzero eigenvalue. For every vector $z \in \mathbb{R}^n$ with $z^Tz = n$,
--
--   $$0 \;\le\; z^T A z \;\le\; \lambda_n\, z^T z \;=\; n\lambda_n \;\le\; \frac{n}{\mathrm{rank}(A)}\,\mathrm{trace}(A)\cdot\kappa_f(A).$$
--
--   Applied to each sample vector $z_i$ of a normalized Rayleigh-quotient estimator, this says every summand $z_i^TAz_i$ lies in the fixed interval $[0,\ \tfrac{n}{\mathrm{rank}(A)}\mathrm{trace}(A)\kappa_f(A)]$, which is what makes Hoeffding's inequality applicable.
--
--   **Formalization Note** The statement is deterministic (a single vector $z$) and records all four links of the displayed chain as a conjunction. $A \ne 0$ guarantees $\mathrm{rank}(A) \ge 1$, so the division by $\mathrm{rank}(A)$ is genuine.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Section 6, proof of Theorem 6.1, display 2

import Mathlib
import Definitions.Def_TraceEstimation_Rayleigh_kappaF

namespace TraceEstimation.Rayleigh

open Matrix

/-- Avron–Toledo, proof of Theorem 6.1 (p. 8:10), second display: for a symmetric positive
semi-definite `A ≠ 0` with largest eigenvalue `λ_n`, and every `z ∈ ℝⁿ` with `zᵀz = n`,
`0 ≤ zᵀAz ≤ λ_n zᵀz = n λ_n ≤ (n / rank(A)) · trace(A) · κ_f(A)`.
This is the deterministic range of one sample of a normalized Rayleigh-quotient estimator. -/
theorem quadratic_form_range {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hA0 : A ≠ 0) (z : Fin n → ℝ) (hz : z ⬝ᵥ z = (n : ℝ)) :
    0 ≤ z ⬝ᵥ (A *ᵥ z) ∧
      z ⬝ᵥ (A *ᵥ z) ≤ lambdaMax hA.isHermitian * (z ⬝ᵥ z) ∧
      lambdaMax hA.isHermitian * (z ⬝ᵥ z) = (n : ℝ) * lambdaMax hA.isHermitian ∧
      (n : ℝ) * lambdaMax hA.isHermitian ≤
        (n : ℝ) / (A.rank : ℝ) * A.trace * kappaF hA.isHermitian := by sorry

end TraceEstimation.Rayleigh
