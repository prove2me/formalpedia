-- Prove2me | Theorems.Thm_ShorNonsmooth_LinearRate_halving_stepsize_linear_rate
-- name    : ShorNonsmooth.LinearRate.halving_stepsize_linear_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:03:23.284233+00:00
-- url     : https://prove2.me/theorems/71560884-3baf-4663-857a-41e3414cc720
-- title:
--   Theorem 2.9 — halving the stepsize every $N \ge 3\sigma^2+1$ steps gives $\|x_k - x^*\| \le 2\sigma h_{k+1}$
-- statement:
--   Let $f$ be a convex function on $E_n$ satisfying the assumptions of Theorem 2.8 with $\sigma \ge 2$: $f$ has a unique minimum point $x^*$, and for the starting point $x_0$ and a number $h_0$
--   $$
--   h_0 \ge \|x_0 - x^*\|/\sigma ,
--   $$
--   and every pair $x, z \in Y = \{y : \|y - x^*\| \le \sigma h_0\}$ with $f(x) = f(z) \ne f(x^*)$ satisfies $\|x - x^*\| \le \sigma\|z - x^*\|$ (2.20). Consider the iteration
--   $$
--   x_{k+1} = x_k - h_{k+1}\frac{g_f(x_k)}{\|g_f(x_k)\|}, \qquad h_{k+1} = h_0\, 2^{-[(k+1)/N]},
--   $$
--   where $[\cdot]$ is the integer part, so that the stepsize stays constant for blocks of $N$ iterations and is then halved. If $N \ge 3\sigma^2 + 1$, then
--   $$
--   \|x_k - x^*\| \le 2\sigma h_{k+1}, \qquad k = 0, 1, 2, \dots \tag{2.24}
--   $$
--
--   Unlike Theorem 2.8, this rule does not need $\sigma$ to compute the stepsizes beyond the block length $N$, and still converges linearly.
--
--   **Formalization Note** "The assumptions of Theorem 2.8" are read with $h_1 = h_0 2^{-[1/N]} = h_0$ (as $N \ge 13$): they give $h_0 \ge \|x_0 - x^*\|/\sigma$ and the ball $Y$ of radius $\sigma h_0$. The book's "if $h_0$ is large enough" is thereby satisfied; the proof opens with the weaker $h_0 \ge \|x_0 - x^*\|/2\sigma$, which alone would leave $x_0$ possibly outside $Y$. The method stops and stays at a point with $g_f(x_k) = 0$ (then $x_k = x^*$).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 34, Theorem 2.9, (2.24); proof p. 35

import Mathlib
import Definitions.Def_ShorNonsmooth_LinearRate_SubgradientMethod

namespace ShorNonsmooth.LinearRate

/-- Shor (1985), p. 34, **Theorem 2.9**. Let `f` satisfy the assumptions of Theorem 2.8 with
`σ ≥ 2`, where the first stepsize is `h₁ = h₀ 2^{-[1/N]} = h₀`: `f` convex on `E_n` with unique
minimum point `x*`, `h₀ ≥ ‖x₀ - x*‖/σ`, and (2.20) on `Y = {y : ‖y - x*‖ ≤ σ h₀}`. Consider the
normalized subgradient method with `h_{k+1} = h₀ 2^{-[(k+1)/N]}` (`[·]` the integer part). If
`N ≥ 3σ² + 1`, then (2.24): `‖x_k - x*‖ ≤ 2 σ h_{k+1}` for all `k = 0, 1, 2, …`.
("`h₀` large enough" is read as the Theorem 2.8 assumption `h₁ ≥ ‖x₀ - x*‖/σ`; it implies the
bound `h₀ ≥ ‖x₀ - x*‖/2σ` with which the proof opens.) -/
theorem halving_stepsize_linear_rate {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xs : EuclideanSpace ℝ (Fin n)) (hxs : ShorNonsmooth.SubgradMethod.MinSet f = {xs})
    (x₀ : EuclideanSpace ℝ (Fin n)) (σ h₀ : ℝ) (N : ℕ)
    (hσ : 2 ≤ σ) (hh₀ : ‖x₀ - xs‖ / σ ≤ h₀)
    (hY : ∀ x ∈ Metric.closedBall xs (σ * h₀), ∀ z ∈ Metric.closedBall xs (σ * h₀),
      f x = f z → f x ≠ f xs → ‖x - xs‖ ≤ σ * ‖z - xs‖)
    (hN : 3 * σ ^ 2 + 1 ≤ (N : ℝ))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) :
    ∀ k, ‖ShorNonsmooth.SubgradMethod.normalizedIter g (fun j => h₀ * (1 / 2 : ℝ) ^ (j / N)) x₀ k - xs‖ ≤
      2 * σ * (h₀ * (1 / 2 : ℝ) ^ ((k + 1) / N)) := by sorry

end ShorNonsmooth.LinearRate
