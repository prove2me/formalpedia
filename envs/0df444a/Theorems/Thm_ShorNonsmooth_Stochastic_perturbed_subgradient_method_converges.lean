-- Prove2me | Theorems.Thm_ShorNonsmooth_Stochastic_perturbed_subgradient_method_converges
-- name    : ShorNonsmooth.Stochastic.perturbed_subgradient_method_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:53:31.01899+00:00
-- url     : https://prove2.me/theorems/3ada756d-edd3-4570-afb8-2ec9ef4016ba
-- title:
--   Theorem 2.20 (Shepilov) — the subgradient method with subgradients at perturbed points converges to a minimum
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex with a nonempty set $M^*$ of minimum points, and let $g_f$ be a subgradient selection ($g_f(x)$ a subgradient of $f$ at $x$ for every $x$). Let $x_0 \in E_n$ be arbitrary and let $\{x_k\}$ satisfy
--   $$
--   x_{k+1} = x_k - h_k \frac{g_f(\tilde x_k)}{\|g_f(\tilde x_k)\|}, \qquad k = 0, 1, 2, \dots,
--   $$
--   where the points $\tilde x_k$ and the numbers $\delta_k$, $h_k$ satisfy
--
--   1. $\|\tilde x_k - x_k\| \le \delta_k$ and $\lim_{k\to\infty} \delta_k = 0$;
--   2. $h_k > 0$, $\sum_{k=0}^\infty h_k \delta_k < \infty$, $\sum_{k=0}^\infty h_k^2 < \infty$, $\sum_{k=0}^\infty h_k = \infty$.
--
--   Then $x_k$ converges to a point $x^* \in M^*$.
--
--   The theorem expresses the stability of the subgradient method with respect to small errors in computing the point at which the subgradient is taken.
--
--   **Formalization Note** The book's formula is undefined when $g_f(\tilde x_k) = 0$ (then $\tilde x_k \in M^*$); in that case the step is skipped, $x_{k+1} = x_k$. When $g_f(\tilde x_k) \ne 0$ for all $k$ this is exactly the book's sequence. The sequences $x_k$, $\tilde x_k$ are given, with the recursion as a hypothesis.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 47, Theorem 2.20

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
open Filter Topology

namespace ShorNonsmooth.Stochastic

/-- Shor (1985), p. 47, **Theorem 2.20** (M. A. Shepilov): let `f` be convex on `E_n` with a
nonempty set `M*` of minima, and `g` a subgradient selection. For any `x₀`, a sequence
`x_{k+1} = x_k - h_k g(x̃_k)/‖g(x̃_k)‖` with `‖x̃_k - x_k‖ ≤ δ_k`, `δ_k → 0`, `h_k > 0`,
`Σ h_k δ_k < ∞`, `Σ h_k² < ∞`, `Σ h_k = ∞` converges to a point of `M*`.
The book's formula is undefined when `g(x̃_k) = 0` (then `x̃_k ∈ M*`); here the step is then
skipped, `x_{k+1} = x_k` (explicit branch, not Lean's `x / 0 = 0`). -/
theorem perturbed_subgradient_method_converges {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hM : (ShorNonsmooth.SubgradMethod.MinSet f).Nonempty)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x))
    (h δ : ℕ → ℝ) (x xt : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : ∀ k, x (k + 1) =
      if g (xt k) = 0 then x k else x k - (h k / ‖g (xt k)‖) • g (xt k))
    (hxt : ∀ k, ‖xt k - x k‖ ≤ δ k) (hδ : Tendsto δ atTop (𝓝 0))
    (hh_pos : ∀ k, 0 < h k) (hhδ : Summable (fun k => h k * δ k))
    (hh_sq : Summable (fun k => h k ^ 2))
    (hh_div : Tendsto (fun N => ∑ k ∈ Finset.range N, h k) atTop atTop) :
    ∃ xstar ∈ ShorNonsmooth.SubgradMethod.MinSet f, Tendsto x atTop (𝓝 xstar) := by sorry

end ShorNonsmooth.Stochastic
