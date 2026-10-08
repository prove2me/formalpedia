-- Prove2me | Theorems.Thm_SherbrookeMetric_PointEstimate_eq10_second_derivative
-- name    : SherbrookeMetric.PointEstimate.eq10_second_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:21.122489+00:00
-- url     : https://prove2.me/theorems/ce4ad160-7606-40c4-8f23-0dd66ba0f1a8
-- title:
--   Eq. (10), p. 139 — $\partial^2 B(s)/\partial\lambda^2 = e^{-\lambda}\lambda^{s-1}/(s-1)! > 0$ for $s \ge 1$, and $0$ for $s = 0$
-- statement:
--   Let $B(s \mid \lambda) = \sum_{x=s+1}^{\infty}(x - s)\,e^{-\lambda}\lambda^x/x!$ be the expected backorders at spare stock $s \in \{0, 1, 2, \dots\}$ under Poisson demand with mean $\lambda$. Fix $\lambda > 0$. Then:
--
--   1. $\mu \mapsto B(s \mid \mu)$ is differentiable at every $\mu > 0$;
--   2. if $s \ge 1$, its derivative is differentiable at $\lambda$ and
--   $$\frac{\partial^2 B(s \mid \lambda)}{\partial \lambda^2} = \frac{e^{-\lambda}\lambda^{s-1}}{(s-1)!} > 0;$$
--   3. if $s = 0$, the second derivative at $\lambda$ exists and equals $0$.
--
--   This is eq. (10) of Sherbrooke (1968) together with the sentence that follows it ("For a spare stock of zero the second derivative is zero"). It is the computation from which the paper concludes that backorders are strictly convex in the mean demand.
--
--   **Formalization Note** The second derivative is stated as `HasDerivAt (deriv (backorders s)) … lam`, together with differentiability of `backorders s` on $(0,\infty)$, so the statement asserts that the second derivative exists and is not a junk value of `deriv`. The exponent and factorial $s - 1$ are natural-number subtraction, used only under $s \ge 1$.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 139, Eq. (10) and the following sentence

import Mathlib
import Definitions.Def_SherbrookeMetric_PointEstimate_backorders

namespace SherbrookeMetric.PointEstimate

/-- Sherbrooke (1968), eq. (10), p. 139, and the sentence after it: for positive mean `lam`,
`B(s | ·)` is differentiable on `(0, ∞)`, its derivative is differentiable at `lam` with
derivative `e^{-λ} λ^{s-1} / (s-1)! > 0` when `s ≥ 1`, and with derivative `0` when `s = 0`. -/
theorem eq10_second_derivative (s : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    (∀ μ : ℝ, 0 < μ → DifferentiableAt ℝ (backorders s) μ) ∧
    (1 ≤ s →
      HasDerivAt (deriv (backorders s))
        (Real.exp (-lam) * lam ^ (s - 1) / ((s - 1).factorial : ℝ)) lam ∧
      0 < Real.exp (-lam) * lam ^ (s - 1) / ((s - 1).factorial : ℝ)) ∧
    (s = 0 → HasDerivAt (deriv (backorders s)) 0 lam) := by sorry

end SherbrookeMetric.PointEstimate
