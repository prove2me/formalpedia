-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_3
-- name    : ProxADMMLC.Conv.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:45.387264+00:00
-- url     : https://prove2.me/theorems/7aa444d7-1546-4d9e-a7ff-cbfeb82f1873
-- title:
--   Lemma 3.3 (proximal descent), p. 2279 — M(z′) − M(z) ≤ p(z′ − z)ᵀ(z − x*(z)) + (pL̃/2)‖z − z′‖², L̃ = p/(p + γ) + 1
-- statement:
--   Let $f$ satisfy Assumption 2.2(c) and (2.4) with constant $\gamma$, let $p>0$ and $p>-\gamma$, and let $x^*(z)$ and $M(z)$ be the minimizer and value of $f(x)+\frac p2\|x-z\|^2$ over $\{x\in P: Ax=b\}$ (2.8)–(2.9). With $\tilde L=\frac p{p+\gamma}+1$, for all $z,z'\in P$,
--   $$M(z')-M(z)\ \le\ p\,(z'-z)^\top\big(z-x^*(z)\big)+\frac{p\tilde L}2\,\|z-z'\|^2.$$
--   In particular, along any run of Algorithm 2.2 (whose iterates $z^t$ lie in $P$),
--   $$M(z^{t+1})-M(z^t)\le p\,(z^{t+1}-z^t)^\top\big(z^t-x^*(z^t)\big)+\frac{p\tilde L}2\|z^t-z^{t+1}\|^2.\tag{3.4}$$
--
--   This is the third descent lemma: $M$ is smooth with gradient $p(z-x^*(z))$ and the stated curvature bound.
--
--   **Formalization Note** The page states (3.4) for the iterates $z^t,z^{t+1}$ of Algorithm 2.2. Those lie in $P$, so the statement here, for any two points of $P$, contains it; it needs no run and no stepsize hypotheses.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2279, Lemma 3.3 (3.4) (proof on p. 2285)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_3 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (p : ℝ) (hp : 0 < p) (hpγ : -γ < p)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ z ∈ box ℓ u, ∀ z' ∈ box ℓ u,
      Mval f p xst z' - Mval f p xst z ≤
        p * inner ℝ (z' - z) (z - xst z) + p * (p / (p + γ) + 1) / 2 * ‖z - z'‖ ^ 2 := by sorry

end ProxADMMLC.Conv
