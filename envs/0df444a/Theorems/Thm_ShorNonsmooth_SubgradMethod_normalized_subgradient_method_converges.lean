-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_normalized_subgradient_method_converges
-- name    : ShorNonsmooth.SubgradMethod.normalized_subgradient_method_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:02:40.790989+00:00
-- url     : https://prove2.me/theorems/82ad8d98-c252-4d7a-9267-67bb6f60d8af
-- title:
--   Theorem 2.2 — the normalized subgradient method with $h_k \to 0$, $\sum h_k = \infty$ converges to $M^*$
-- statement:
--   Let $f$ be a convex function on $E_n$ whose set $M^*$ of minimum points is nonempty and bounded, and let $f^* = \min_{x \in E_n} f(x)$. Let $h_1, h_2, \dots$ be positive numbers with
--   $$
--   \lim_{k \to \infty} h_k = 0, \qquad \sum_{k=1}^{\infty} h_k = +\infty .
--   $$
--   For any starting point $x_0 \in E_n$ and any choice of subgradients $g_f(x_k)$, consider the sequence
--   $$
--   x_{k+1} = x_k - h_{k+1}\,\frac{g_f(x_k)}{\|g_f(x_k)\|}, \qquad k = 0, 1, \dots \tag{2.4}
--   $$
--   Then either some $x_{\bar k}$ belongs to $M^*$, or
--   $$
--   \lim_{k\to\infty} \min_{y \in M^*} \|x_k - y\| = 0 \quad\text{and}\quad \lim_{k \to \infty} f(x_k) = f^* .
--   $$
--
--   This is the basic convergence theorem for the subgradient method on a general convex function: no smoothness, no Lipschitz constant and no bound on the subgradients are assumed.
--
--   **Formalization Note** The book writes "bounded set of minimum points" and uses $\min_{y\in M^*}$ and $f^* = \min f$, which presuppose $M^* \neq \emptyset$; nonemptiness is an explicit hypothesis. $\min_{y\in M^*}\|x_k - y\|$ is `Metric.infDist`, and $f^*$ is $\inf f$ (attained). The stepsizes are `h : ℕ → ℝ` with `h (k+1)` used at step $k$; positivity is required for $k \ge 1$ only and divergence is of $\sum_{k \ge 1} h_k$. The subgradient selection and the starting point are arbitrary. If $g_f(x_k) = 0$ the sequence stays at $x_k \in M^*$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 25, Theorem 2.2

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 25, Theorem 2.2. Let `f` be convex on `E_n` with a bounded (and, as the
book presupposes, nonempty) set `M*` of minimum points, and let `h_k > 0`, `k = 1, 2, …`, with
`h_k → 0` and `∑_{k≥1} h_k = +∞`. Then for any `x₀ ∈ E_n` and any subgradient selection, the
sequence `x_{k+1} = x_k - h_{k+1} g_f(x_k)/‖g_f(x_k)‖` (2.4) either hits `M*` at some index `k̄`,
or satisfies `min_{y ∈ M*} ‖x_k - y‖ → 0` and `f(x_k) → min f = f*`. -/
theorem normalized_subgradient_method_converges {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k + 1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k + 1)) atTop atTop)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (∃ kbar : ℕ, normalizedIter g h x₀ kbar ∈ MinSet f) ∨
      (Tendsto (fun k => Metric.infDist (normalizedIter g h x₀ k) (MinSet f)) atTop (𝓝 0) ∧
        Tendsto (fun k => f (normalizedIter g h x₀ k)) atTop (𝓝 (⨅ y, f y))) := by sorry

end ShorNonsmooth.SubgradMethod
