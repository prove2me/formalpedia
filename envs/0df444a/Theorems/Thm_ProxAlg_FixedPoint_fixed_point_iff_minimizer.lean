-- Prove2me | Theorems.Thm_ProxAlg_FixedPoint_fixed_point_iff_minimizer
-- name    : ProxAlg.FixedPoint.fixed_point_iff_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:55.060981+00:00
-- url     : https://prove2.me/theorems/24d025ba-a5ab-4ce5-a83a-09920f813537
-- title:
--   §2.3, p. 130 — minimizers of f are exactly fixed points of prox_{λf}
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be closed, proper and convex, and let $\lambda>0$. A point $x^\star\in\mathbb R^n$ minimizes $f$ if and only if it is a fixed point of the proximal operator of $\lambda f$:
--   $$
--   f(x^\star)\le f(y)\quad\text{for every }y\in\mathbb R^n
--   \quad\Longleftrightarrow\quad
--   x^\star=\operatorname{prox}_{\lambda f}(x^\star).
--   $$
--
--   This identifies the optimization problem with a fixed-point problem. The paper prints the case $\lambda=1$ and explicitly observes that positive scaling leaves minimizers unchanged.
--
--   **Formalization Note** The function $\lambda f$ is the extended-real pointwise product, with $\lambda>0$ ensuring that $\lambda(+\infty)=+\infty$.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §2.3, p. 130, opening fixed-point statement and parenthesis

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace ProxAlg.FixedPoint

theorem fixed_point_iff_minimizer {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : MoreauProx.Decomposition.GammaZero f) (lam : ℝ) (hlam : 0 < lam)
    (xs : EuclideanSpace ℝ (Fin n)) :
    (∀ y, f xs ≤ f y) ↔
      MoreauProx.Decomposition.IsProx (fun u => ((lam : ℝ) : EReal) * f u) xs xs := by sorry

end ProxAlg.FixedPoint
