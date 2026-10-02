-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_dist_sq_step_le
-- name    : ShorNonsmooth.SubgradMethod.dist_sq_step_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:00:06.632765+00:00
-- url     : https://prove2.me/theorems/397a7474-fb21-474f-bcf3-3038cebaf9ba
-- title:
--   Eq. (2.3) — one normalized step: $\|x_{k+1}-x^*\|^2 \le \|x_k-x^*\|^2 + h^2 - 2h\,\rho(x^*,U_k)$
-- statement:
--   Let $f$ be a convex function on $E_n$, let $x^*$ be a minimum point of $f$, and let $g_k \neq 0$ be a subgradient of $f$ at a point $x_k$. Let $U_k = \{x : f(x) = f(x_k)\}$ be the level surface of $f$ through $x_k$ and $b_k(x^*) = \rho(x^*, U_k) = \inf_{u \in U_k} \|x^* - u\|$ the distance from $x^*$ to it. For $h > 0$ put $x_{k+1} = x_k - h\, g_k / \|g_k\|$. Then
--   $$
--   \|x_{k+1} - x^*\|^2 \le \|x_k - x^*\|^2 + h^2 - 2h\, b_k(x^*).
--   $$
--
--   This one-step inequality is used in every convergence proof of Sections 2.1–2.2: a normalized step of length $h$ brings the iterate closer to $x^*$ as soon as the level surface through $x_k$ is farther than $h/2$ from $x^*$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 24, inequality (2.3) (with U_k and b_k(x*) defined on p. 24)

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 24, inequality (2.3) (with `U_k = {x : f(x) = f(x_k)}` and
`b_k(x*) = ρ(x*, U_k)` defined just before it). Let `f` be convex on `E_n`, `x* ∈ M*`, and let
`g_k ≠ 0` be a subgradient of `f` at `x_k`. For a step `x_{k+1} = x_k - h g_k / ‖g_k‖` with
`h > 0`,
`‖x_{k+1} - x*‖² ≤ ‖x_k - x*‖² + h² - 2 h ρ(x*, U_k)`. -/
theorem dist_sq_step_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (xk gk xstar : EuclideanSpace ℝ (Fin n))
    (hgk : ShorNonsmooth.AlmostDiff.IsSubgradient f xk gk) (hgk0 : gk ≠ 0) (hxstar : xstar ∈ MinSet f)
    (h : ℝ) (hh : 0 < h) :
    ‖xk - (h / ‖gk‖) • gk - xstar‖ ^ 2 ≤
      ‖xk - xstar‖ ^ 2 + h ^ 2 - 2 * h * Metric.infDist xstar {x | f x = f xk} := by sorry

end ShorNonsmooth.SubgradMethod
