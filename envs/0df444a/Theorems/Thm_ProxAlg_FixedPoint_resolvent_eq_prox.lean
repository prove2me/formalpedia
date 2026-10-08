-- Prove2me | Theorems.Thm_ProxAlg_FixedPoint_resolvent_eq_prox
-- name    : ProxAlg.FixedPoint.resolvent_eq_prox
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:08.674764+00:00
-- url     : https://prove2.me/theorems/92fe9493-ae8e-466b-9ede-f6aa20e6ca8b
-- title:
--   (3.4), pp. 137–138 — prox_{λf} is the full-domain single-valued resolvent of ∂f
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be closed, proper and convex, and let $\lambda>0$. For $x,z\in\mathbb R^n$, the relation $x\in z+\lambda\partial f(z)$ holds exactly when $z$ is the proximal point of $x$ for $\lambda f$:
--   $$
--   x\in z+\lambda\partial f(z)
--   \quad\Longleftrightarrow\quad
--   z=\operatorname{prox}_{\lambda f}(x).
--   $$
--   Moreover, for every $x$ there is exactly one such $z$. Thus the relation $(I+\lambda\partial f)^{-1}$ has full domain and a single value at each input, and equals $\operatorname{prox}_{\lambda f}$.
--
--   The identity makes the proximal operator the resolvent of the subdifferential, the connection used in the forward-backward fixed-point expression.
--
--   **Formalization Note** The resolvent relation is expanded as an existential subgradient; the uniqueness and full-domain statement is the second conjunct. The extended-real scalar product uses $\lambda>0$.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §3.2, pp. 137–138, (3.4) and proof

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace ProxAlg.FixedPoint

theorem resolvent_eq_prox {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : MoreauProx.Decomposition.GammaZero f) (lam : ℝ) (hlam : 0 < lam) :
    (∀ x z : EuclideanSpace ℝ (Fin n),
      (∃ y ∈ subdifferential f z, x = z + lam • y) ↔
        MoreauProx.Decomposition.IsProx (fun u => ((lam : ℝ) : EReal) * f u) x z) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      ∃! z : EuclideanSpace ℝ (Fin n), ∃ y ∈ subdifferential f z, x = z + lam • y) := by sorry

end ProxAlg.FixedPoint
