-- Prove2me | Theorems.Thm_TraceEstimation_Gaussian_mgf_formula
-- name    : TraceEstimation.Gaussian.mgf_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:28:14.611927+00:00
-- url     : https://prove2.me/theorems/32d5ac6e-0148-4907-9f8d-c66794011fa7
-- title:
--   Section 5, Eq. (1) — moment generating function of $Z = M G_M$
-- statement:
--   Let $A$ be an $n \times n$ real symmetric matrix with eigenvalues $\lambda_1, \ldots, \lambda_n$ (listed with multiplicity), let $\tau = \mathrm{trace}(A)$, let $M \ge 1$, and let $G_M$ be the Gaussian trace estimator with $M$ samples. Put $Z = M G_M$. For every real $t$ with $2\lambda_i t < 1$ for all $i$, the moment generating function of $Z$ is
--
--   $$m_Z(t) = \mathrm{E}(\exp(tZ)) = \prod_{i=1}^{n}(1 - 2\lambda_i t)^{-M/2} = (1 - 2\tau t + h(t))^{-M/2},$$
--
--   where $h(t) = \sum_{s=2}^{n}(-2)^s t^s \sum_{S \subseteq [n],\,|S| = s} \prod_{i\in S} \lambda_i$.
--
--   This is the moment generating function on which the Chernoff argument for Theorem 5.2 rests.
--
--   **Formalization Note** The paper states the formula "as long as $|\lambda_i t| \le \frac12$ for all $i$". At $\lambda_i t = \frac12$ the base $1 - 2\lambda_i t$ is $0$ and the expectation is infinite, while Lean's real power `0 ^ (-M/2)` is $0$; the statement therefore uses the open range $2\lambda_i t < 1$, which is where the formula holds (it also covers negative $t$ and negative eigenvalues). The moment generating function is Mathlib's `mgf`, and the eigenvalues are `Matrix.IsHermitian.eigenvalues`.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), pp. 8:7-8:8, Section 5, Eq. (1)

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator
import Definitions.Def_TraceEstimation_Gaussian_hPoly

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

/-- Section 5, Eq. (1) (Avron–Toledo, pp. 8:7–8:8). Let `A` be symmetric with eigenvalues
`λ_1, …, λ_n` (with multiplicity) and `τ = trace(A)`. If `2 λ_i t < 1` for every `i`, the
moment generating function of `Z = M · G_M` at `t` is
`∏_i (1 - 2 λ_i t)^{-M/2} = (1 - 2 τ t + h(t))^{-M/2}`.
The page's range `|λ_i t| ≤ 1/2` includes `1 - 2 λ_i t = 0`, where the mgf is infinite; the
strict inequality is the range where the formula holds. -/
theorem mgf_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : ∀ i, 2 * hA.eigenvalues i * t < 1) :
    mgf (fun ω => (M : ℝ) * Shared.gaussianEstimator A M ω) (Shared.gaussianSampleMeasure n M) t =
      ∏ i : Fin n, (1 - 2 * hA.eigenvalues i * t) ^ (-(M : ℝ) / 2) ∧
    mgf (fun ω => (M : ℝ) * Shared.gaussianEstimator A M ω) (Shared.gaussianSampleMeasure n M) t =
      (1 - 2 * A.trace * t + hPoly hA.eigenvalues t) ^ (-(M : ℝ) / 2) := by sorry

end TraceEstimation.Gaussian
