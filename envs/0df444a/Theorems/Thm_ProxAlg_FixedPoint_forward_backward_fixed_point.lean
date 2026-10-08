-- Prove2me | Theorems.Thm_ProxAlg_FixedPoint_forward_backward_fixed_point
-- name    : ProxAlg.FixedPoint.forward_backward_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:03.824982+00:00
-- url     : https://prove2.me/theorems/cdcb1ab6-a580-4fba-8cf4-bcfda131b294
-- title:
--   §4.2.1, pp. 150–151 — minimizers of f + g are fixed points of the forward-backward operator
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable and convex, and let $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be closed, proper and convex. For any $\lambda>0$ and any $x^\star\in\mathbb R^n$,
--   $$
--   (f+g)(x^\star)\le(f+g)(y)\quad\text{for every }y\in\mathbb R^n
--   \quad\Longleftrightarrow\quad
--   x^\star=\operatorname{prox}_{\lambda g}\bigl(x^\star-\lambda\nabla f(x^\star)\bigr).
--   $$
--
--   The fixed points of the forward-backward operator are precisely the solutions of the composite convex minimization problem (4.5). The statement holds for every positive step size; a smaller step size is required only for the convergence claim later on p. 151.
--
--   **Formalization Note** The right side is Moreau's proximal-minimizer predicate, not a choice function. It minimizes $\tfrac12\|u-v\|_2^2+\lambda g(u)$; since $\lambda>0$, this has the same minimizers as (1.2), $g(u)+\tfrac1{2\lambda}\|u-v\|_2^2$. The gradient is Mathlib's Euclidean gradient, defined here because $f$ is differentiable everywhere. The inner product and norm are Euclidean on $\mathbb R^n$.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §4.2.1, pp. 150–151, 'Fixed point iteration'

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace ProxAlg.FixedPoint

theorem forward_backward_fixed_point {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : MoreauProx.Decomposition.GammaZero g)
    (lam : ℝ) (hlam : 0 < lam) (xs : EuclideanSpace ℝ (Fin n)) :
    (∀ y, ((f xs : ℝ) : EReal) + g xs ≤ ((f y : ℝ) : EReal) + g y) ↔
      MoreauProx.Decomposition.IsProx
        (fun u => ((lam : ℝ) : EReal) * g u)
        (xs - lam • gradient f xs) xs := by sorry

end ProxAlg.FixedPoint
