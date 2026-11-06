-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_11
-- name    : RollingProbeQN.Convex.lemma_D_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:39.783318+00:00
-- url     : https://prove2.me/theorems/1158346c-da17-4264-aa58-46a27a6626a1
-- title:
--   Lemma D.11 — finite-difference error $\le L_2\tau/2$
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ have an $L_2$-Lipschitz Hessian. For every $y$, every $\tau>0$ and every unit vector $v$,
--
--   $$\Big\|\frac{\nabla F(y+\tau v)-\nabla F(y)}{\tau}-\nabla^2F(y)\,v\Big\|\ \le\ \frac{L_2\tau}{2}.$$
--
--   This is the accuracy of one gradient difference as a Hessian-vector product.
--
--   Differences from the source:
--   - encoding: a function with an L₂-Lipschitz Hessian → ContDiff ℝ 2 F and ‖hess F x − hess F y‖ ≤ L₂‖x − y‖; reason: a Lipschitz Hessian exists and is continuous, so F is C²; same functions
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.11, p. 41

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_hess

namespace RollingProbeQN.Convex

/-- **Lemma D.11 (Finite-difference error).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.11, p. 41: "For a function `F` with `L2`-Lipschitz Hessian, any `τ > 0`, and any unit
vector `v`, `‖(∇F(y + τv) − ∇F(y))/τ − ∇²F(y)v‖ ≤ L2τ/2`."

**Formalization Note.** "A function with an `L₂`-Lipschitz Hessian" is `ContDiff ℝ 2 F` together
with the Lipschitz bound on `hess F` in operator norm. -/
theorem lemma_D_11 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ} {L₂ : ℝ} (hF : ContDiff ℝ 2 F)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin d), ‖hess F x - hess F y‖ ≤ L₂ * ‖x - y‖)
    (y v : EuclideanSpace ℝ (Fin d)) (τ : ℝ) (hτ : 0 < τ) (hv : ‖v‖ = 1) :
    ‖τ⁻¹ • (gradient F (y + τ • v) - gradient F y) - hess F y v‖ ≤ L₂ * τ / 2 := by sorry

end RollingProbeQN.Convex
