-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_eq_3_12_dist
-- name    : ProxADMMLC.Conv.eq_3_12_dist
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-05T18:48:52.899201+00:00
-- url     : https://prove2.me/theorems/551961c0-a3a9-46ff-871d-22aa68bfdfff
-- title:
--   (3.12) at a multiplier, p. 2282 — (p + γ)‖x(y, z) − x*(z)‖ ≤ ‖A‖ dist(y, Y*(z))
-- statement:
--   Suppose Assumption 2.2(c) holds with constant $L$, $\gamma$ satisfies (2.4), $\Gamma>0$, $p>0$ and $p>-\gamma$. Let $x(y,z)$ and $x^*(z)$ be as in (2.7) and (2.9), and let $Y^*(z)$ be the set of dual multipliers of the equality constraint of the proximal problem (2.8) at $x^*(z)$, i.e. the $w$ for which (3.16) holds with some $\mu,\nu\succeq 0$. Then for every $z\in P$ and every $y\in\mathbb R^m$,
--   $$\frac{p+\gamma}{\sigma}\,\|x(y,z)-x^*(z)\|\ \le\ \operatorname{dist}(y,Y^*(z)),\qquad \sigma=\|A\|,$$
--   written without division as $(p+\gamma)\|x(y,z)-x^*(z)\|\le \|A\|\,\operatorname{dist}(y,Y^*(z))$.
--
--   Role: this is the error bound (3.12) of Lemma 3.10 applied with $y'\in Y^*(z)$, for which $x(y',z)=x^*(z)$. In the proof of Theorem 2.4 (Case 1, (3.31)) it converts the dual error bound (3.15) into a bound on $\|x(y^{t+1},z^t)-x^*(z^t)\|$.
--
--   **Formalization Note**: the statement includes that $Y^*(z)$ is nonempty (the multipliers of the linearly constrained problem (2.8) exist); with an empty set Mathlib's `Metric.infDist` would be $0$.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), https://arxiv.org/abs/1812.10229, Lemma 3.10 (3.12) with y' in Y*(z) as in (3.15)-(3.16), p. 2282; used in (3.31), p. 2288

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem eq_3_12_dist {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ z ∈ box ℓ u, ∀ y : E m,
      (p + γ) * ‖xs y z - xst z‖ ≤ ‖A‖ * Metric.infDist y (Ystar f A ℓ u p xst z) := by sorry

end ProxADMMLC.Conv
