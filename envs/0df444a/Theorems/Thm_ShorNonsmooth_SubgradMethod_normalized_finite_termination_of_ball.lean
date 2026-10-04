-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_normalized_finite_termination_of_ball
-- name    : ShorNonsmooth.SubgradMethod.normalized_finite_termination_of_ball
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:04:22.364406+00:00
-- url     : https://prove2.me/theorems/7ec298c0-ab38-4bc8-8518-c3d0ce7b0afd
-- title:
--   Theorem 2.5 — if $M^*$ contains a ball of radius $r$ and $\limsup h_k < 2r$, the method (2.4) terminates
-- statement:
--   Let $f$ be a convex function on $E_n$ whose set $M^*$ of minimum points contains a ball $S_r$ of radius $r > 0$. Let the stepsizes $h_k > 0$ satisfy
--   $$
--   \sum_{k=0}^{\infty} h_k = +\infty \qquad\text{and}\qquad \limsup_{k \to \infty} h_k < 2r .
--   $$
--   Then for every starting point $x_0 \in E_n$ and every choice of subgradients, the normalized subgradient method (2.4), $x_{k+1} = x_k - h_{k+1} g_f(x_k)/\|g_f(x_k)\|$, reaches $M^*$ after finitely many steps: there is an index $k(x_0)$ with $x_{k(x_0)} \in M^*$.
--
--   Stepsizes need not tend to zero here; it suffices that they are eventually shorter than the diameter of a ball of minimizers.
--
--   **Formalization Note** $\limsup h_k < 2r$ is encoded as "there is $q < 2r$ with $h_k \le q$ for all large $k$", which is equivalent for real sequences and excludes unbounded sequences (whose `Filter.limsup` in `ℝ` is a junk value). The ball is `Metric.closedBall c r`. The book's sum starts at $k = 0$; $h_0$ does not enter the iteration and does not affect divergence.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 27, Theorem 2.5

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 27, Theorem 2.5. Suppose the set `M*` of minimum points of the convex
function `f` contains a ball (the book's "sphere") `S_r` of radius `r > 0`, and the normalized
subgradient method (2.4) uses stepsizes `h_k > 0` with `∑_{k≥0} h_k = +∞` and
`limsup_{k→∞} h_k < 2r` (encoded as: for some `q < 2r`, eventually `h_k ≤ q`). Then for any
`x₀ ∈ E_n` (and any subgradient selection) some iterate `x_{k(x₀)}` lies in `M*`. -/
theorem normalized_finite_termination_of_ball {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ MinSet f) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h k)
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h k) atTop atTop)
    (hlimsup : ∃ q < 2 * r, ∀ᶠ k in atTop, h k ≤ q)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℕ, normalizedIter g h x₀ k ∈ MinSet f := by sorry

end ShorNonsmooth.SubgradMethod
