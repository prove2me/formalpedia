-- Prove2me | Theorems.Thm_VarianceRegularization_Expansion_exact_variance_expansion
-- name    : VarianceRegularization.Expansion.exact_variance_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:53:53.089342+00:00
-- url     : https://prove2.me/theorems/3d62f3cf-12bc-4501-891f-ce3871c9b6b1
-- title:
--   Theorem 1, (11): high-probability exact variance expansion, corrected threshold
-- statement:
--   Let $Z$ have probability law $P$ supported on $[M_0,M_1]$, set $M=M_1-M_0$, and let its population variance be $\sigma^2>0$. Draw $n\ge1$ independent values with law $P$, and fix $\rho\ge0$. If
--
--   $$n\ge\max\left\{5,\frac{M^2}{\sigma^2}\max\{8\sigma,44,44\rho\}\right\},$$
--
--   then the probability that the χ² robust expectation differs from the empirical mean plus its standard-deviation penalty is at most
--
--   $$\Pr\left\{R_n(Z_{1:n},\rho)\ne\bar Z+\sqrt{\frac{2\rho s_n^2}{n}}\right\}\le\exp\left(-\frac{n\sigma^2}{11M^2}\right).$$
--
--   Thus the robust value equals the variance-regularized value with the stated confidence at this sample size.
--
--   **Formalization Note** The paper prints $n\ge\max\{5,(M^2/\sigma^2)\max\{8\sigma,44\}\}$, omitting the $44\rho$ term. Its proof on p. 32 invokes $n\ge44\rho M^2/\sigma^2$, and the printed claim is false for large $\rho$; for Bernoulli$(1/2)$, $n=176$ and $\rho=n(n-1)/2$ give a counterexample. The Lean conclusion measures the bad event under the product law, using outer measure if needed. Positive variance makes every division meaningful.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 7, Theorem 1, equality (11); corrected using Appendix A, p. 32

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_robustSup
import Definitions.Def_VarianceRegularization_Expansion_empVar

open MeasureTheory

namespace VarianceRegularization.Expansion

/-- Theorem 1, (11), p. 7, with the missing `ρ` threshold supplied from the proof on p. 32.
The printed sample-size condition omits `n ≥ 44ρ M²/σ²`; the proof invokes it. For example,
Bernoulli(1/2), `n = 176`, and `ρ = n(n-1)/2` violate printed (11) on almost every sample.
Here the sample is drawn from the product law, and its bad-event measure is outer probability. -/
theorem exact_variance_expansion {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hsupp : P (Set.Icc M₀ M₁) = 1)
    (hvar : 0 < ProbabilityTheory.variance (id : ℝ → ℝ) P)
    (hsize : max 5 (((M₁ - M₀) ^ 2 /
        ProbabilityTheory.variance (id : ℝ → ℝ) P) *
        max (8 * Real.sqrt (ProbabilityTheory.variance (id : ℝ → ℝ) P))
          (max 44 (44 * ρ))) ≤ (n : ℝ)) :
    (Measure.pi (fun _ : Fin n => P))
        {z : Fin n → ℝ |
          robustSup n ρ z ≠
            empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z)} ≤
      ENNReal.ofReal (Real.exp
        (-(n : ℝ) * ProbabilityTheory.variance (id : ℝ → ℝ) P /
          (11 * (M₁ - M₀) ^ 2))) := by sorry

end VarianceRegularization.Expansion
