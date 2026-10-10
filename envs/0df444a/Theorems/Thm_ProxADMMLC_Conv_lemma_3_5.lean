-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_5
-- name    : ProxADMMLC.Conv.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:39.900043+00:00
-- url     : https://prove2.me/theorems/b781ee79-2b3a-4272-9520-67313d3c5e99
-- title:
--   Lemma 3.5, p. 2280 — x*(·) and x(y, ·) are p/(p + γ)-Lipschitz on P; ‖x(y, z) − x(y′, z)‖ ≤ (σ/(p + γ))‖y − y′‖
-- statement:
--   Let $f$ satisfy Assumption 2.2(c) and (2.4) with constant $\gamma$, let $\Gamma>0$, $p>0$ and $p>-\gamma$, and let $x(y,z)$ and $x^*(z)$ be the minimizers (2.7) and (2.9). Write $\sigma=\|A\|$. Then for all $z,z'\in P$ and all $y,y'\in\mathbb R^m$:
--   1. $\displaystyle\|x^*(z)-x^*(z')\|\le\frac p{p+\gamma}\|z-z'\|$;
--   2. $\displaystyle\|x(y,z)-x(y,z')\|\le\frac p{p+\gamma}\|z-z'\|$;
--   3. $\displaystyle(p+\gamma)\,\|x(y,z)-x(y',z)\|\le\sigma\,\|y-y'\|$.
--
--   These Lipschitz bounds are the error bounds (3.12)–(3.14) of Lemma 3.10, and give the Lipschitz continuity of $\nabla M$ used in Lemma 3.3.
--
--   **Formalization Note** The page prints the third bound as $\|x(y,z)-x(y',z)\|\le\frac{p+\gamma}{\sigma}\|y-y'\|$. Lemma 3.10 states the same bound as (3.12), $\|y-y'\|\ge\sigma_3\|x(y,z)-x(y',z)\|$ with $\sigma_3=(\gamma+p)/\sigma$, and says "(3.12), (3.13), and (3.14) are just Lemma 3.5"; the correct constant is therefore $\sigma/(p+\gamma)$, which is stated here, multiplied out so that $A=0$ needs no division.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2280, Lemma 3.5 (third constant as in (3.12), p. 2282)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_5 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ z ∈ box ℓ u, ∀ z' ∈ box ℓ u, ∀ y y' : E m,
      ‖xst z - xst z'‖ ≤ p / (p + γ) * ‖z - z'‖ ∧
      ‖xs y z - xs y z'‖ ≤ p / (p + γ) * ‖z - z'‖ ∧
      (p + γ) * ‖xs y z - xs y' z‖ ≤ ‖A‖ * ‖y - y'‖ := by sorry

end ProxADMMLC.Conv
