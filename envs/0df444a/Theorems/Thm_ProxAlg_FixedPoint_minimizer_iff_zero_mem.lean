-- Prove2me | Theorems.Thm_ProxAlg_FixedPoint_minimizer_iff_zero_mem
-- name    : ProxAlg.FixedPoint.minimizer_iff_zero_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:01.135956+00:00
-- url     : https://prove2.me/theorems/e084eb7f-20f5-476a-8cb9-5b952a09d23c
-- title:
--   §4.2.1, p. 150 — optimality of f + g is 0 ∈ ∇f(x) + ∂g(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable and convex, and let $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be closed, proper and convex. A point $x^\star$ minimizes their sum exactly when the negative gradient of $f$ is a subgradient of $g$ there:
--   $$
--   (f+g)(x^\star)\le(f+g)(y)\quad\text{for all }y\in\mathbb R^n
--   \quad\Longleftrightarrow\quad
--   0\in\nabla f(x^\star)+\partial g(x^\star).
--   $$
--
--   This is the first-order condition on which the paper bases the fixed-point interpretation of proximal gradient.
--
--   **Formalization Note** The real-valued $f$ is finite everywhere, so its convex epigraph is closed and it is proper. No Lipschitz condition on $\nabla f$ is needed for this optimality statement. Values of $f+g$ are compared in `EReal`.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §4.2.1, p. 150, first displayed optimality condition

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace ProxAlg.FixedPoint

theorem minimizer_iff_zero_mem {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : MoreauProx.Decomposition.GammaZero g)
    (xs : EuclideanSpace ℝ (Fin n)) :
    (∀ y, ((f xs : ℝ) : EReal) + g xs ≤ ((f y : ℝ) : EReal) + g y) ↔
      ∃ v ∈ subdifferential g xs, gradient f xs + v = 0 := by sorry

end ProxAlg.FixedPoint
