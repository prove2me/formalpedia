-- Prove2me | Theorems.Thm_ShorNonsmooth_Stochastic_nonconvex_reset_method_converges
-- name    : ShorNonsmooth.Stochastic.nonconvex_reset_method_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:53:51.31443+00:00
-- url     : https://prove2.me/theorems/484618ef-f730-4e6e-b732-c5c6ecd28345
-- title:
--   Theorem 2.18 (Bazhenov) — the subgradient method with restarts converges to a local minimum of an almost differentiable function
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be almost differentiable and let $g_f(x) \in G_f(x)$ be an almost-gradient of $f$ at every $x$. Let $r > 0$, $S_r = \{x : \|x - x^*\| \le r\}$, and let $x^*$ be a local minimum point of $f$ with
--   $$
--   f(x^*) = \min_{x \in S_r} f(x).
--   $$
--   Suppose that for every $\varepsilon$ with $0 < \varepsilon < r$,
--   $$
--   \inf_{x \in S_r \setminus S_\varepsilon} \big(g_f(x),\, x - x^*\big) > 0 .
--   $$
--   If $\|x_0 - x^*\| \le r$ and $h_k > 0$, $\lim_{k\to\infty} h_k = 0$, $\sum_{k=0}^\infty h_k = +\infty$, then the sequence
--   $$
--   x_{k+1} = \begin{cases} \bar x_{k+1} & \text{if } \bar x_{k+1} \in S_r, \\ x_0 & \text{if } \bar x_{k+1} \notin S_r, \end{cases} \qquad
--   \bar x_{k+1} = x_k - h_k \frac{g_f(x_k)}{\|g_f(x_k)\|},
--   $$
--   converges to $x^*$.
--
--   The infimum condition replaces, for nonconvex functions, the property of convex functions that the angle between the subgradient and the direction towards the minimum is obtuse.
--
--   **Formalization Note** "$\inf > 0$" is rendered as the existence of $\eta > 0$ with $(g_f(x), x - x^*) \ge \eta$ on $S_r \setminus S_\varepsilon = \{\varepsilon < \|x - x^*\| \le r\}$. When $g_f(x_k) = 0$ (possible only at $x_k = x^*$) the sequence stays at $x_k$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 45, Theorem 2.18

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_NonconvexMethod
open Filter Topology

namespace ShorNonsmooth.Stochastic

/-- Shor (1985), p. 45, **Theorem 2.18** (L. G. Bazhenov): let `f` be almost differentiable and
`g` a selection of almost-gradients (`g x ∈ G_f(x)`). Let `xstar` be a local minimum point with
`f(xstar) = min_{x ∈ S_r} f(x)`, `S_r = {x : ‖x - xstar‖ ≤ r}`, `r > 0`, and suppose that for
every `0 < ε < r`, `inf_{x ∈ S_r ∖ S_ε} (g(x), x - xstar) > 0` (a positive lower bound `η`).
If `‖x₀ - xstar‖ ≤ r`, `h_k > 0`, `h_k → 0`, `Σ h_k = +∞`, the sequence `resetIter`
(`x_{k+1} = x̄_{k+1}` if `x̄_{k+1} ∈ S_r`, else `x₀`; `x̄_{k+1} = x_k - h_k g(x_k)/‖g(x_k)‖`)
converges to `xstar`. -/
theorem nonconvex_reset_method_converges {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ShorNonsmooth.AlmostDiff.AlmostDifferentiable f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, g x ∈ ShorNonsmooth.AlmostDiff.almostGradients f x)
    (xstar : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (hmin : ∀ x, ‖x - xstar‖ ≤ r → f xstar ≤ f x)
    (hangle : ∀ ε, 0 < ε → ε < r → ∃ η > 0, ∀ x, ε < ‖x - xstar‖ → ‖x - xstar‖ ≤ r →
      η ≤ inner ℝ (g x) (x - xstar))
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : ‖x₀ - xstar‖ ≤ r)
    (h : ℕ → ℝ) (hh_pos : ∀ k, 0 < h k) (hh_lim : Tendsto h atTop (𝓝 0))
    (hh_div : Tendsto (fun N => ∑ k ∈ Finset.range N, h k) atTop atTop) :
    Tendsto (resetIter g h xstar r x₀) atTop (𝓝 xstar) := by sorry

end ShorNonsmooth.Stochastic
