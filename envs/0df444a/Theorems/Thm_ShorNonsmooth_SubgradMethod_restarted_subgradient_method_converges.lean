-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_restarted_subgradient_method_converges
-- name    : ShorNonsmooth.SubgradMethod.restarted_subgradient_method_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:03:49.556988+00:00
-- url     : https://prove2.me/theorems/d6e53755-2608-4046-8ea4-f0a3bca650ac
-- title:
--   Theorem 2.4 — the subgradient method restarted at $x_0$ when $h_{k+1}\|g_f(x_k)\| > c$ converges
-- statement:
--   Let $f$ be a convex function on $E_n$ whose set $M^*$ of minimum points is nonempty and bounded, $f^* = \min f$, and let $h_k > 0$, $h_k \to 0$, $\sum_{k=1}^\infty h_k = +\infty$. Let $c > 0$ be a constant. For any starting point $x_0$ and any choice of subgradients, the sequence
--   $$
--   x_{k+1} = \begin{cases} x_k - h_{k+1}\, g_f(x_k) & \text{if } h_{k+1}\|g_f(x_k)\| \le c, \\ x_0 & \text{otherwise,} \end{cases}
--   $$
--   satisfies
--   $$
--   \lim_{k\to\infty} \min_{x \in M^*} \|x_k - x\| = 0, \qquad \lim_{k\to\infty} f(x_k) = f^* .
--   $$
--
--   Restarting from $x_0$ whenever a step would be longer than $c$ removes the boundedness requirement of Theorem 2.3 without normalizing the subgradients.
--
--   **Formalization Note** The restart goes back to the original starting point $x_0$, not to $x_k$. Nonemptiness of $M^*$ is explicit, as in Theorem 2.2.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 27, Theorem 2.4

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 27, Theorem 2.4. Under the assumptions of Theorem 2.2 (`f` convex on `E_n`,
`M*` nonempty and bounded, `h_k > 0`, `h_k → 0`, `∑_{k≥1} h_k = +∞`), for any positive constant
`c`, any starting point `x₀` and any subgradient selection, the sequence
`x_{k+1} = x_k - h_{k+1} g_f(x_k)` if `h_{k+1} ‖g_f(x_k)‖ ≤ c`, `x_{k+1} = x₀` otherwise,
satisfies `min_{x ∈ M*} ‖x_k - x‖ → 0` and `f(x_k) → f*`. -/
theorem restarted_subgradient_method_converges {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k + 1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k + 1)) atTop atTop)
    (c : ℝ) (hc : 0 < c)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => Metric.infDist (resetIter g h c x₀ k) (MinSet f)) atTop (𝓝 0) ∧
      Tendsto (fun k => f (resetIter g h c x₀ k)) atTop (𝓝 (⨅ y, f y)) := by sorry

end ShorNonsmooth.SubgradMethod
