-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_eq_3_37
-- name    : ProxADMMLC.Conv.eq_3_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:42.032709+00:00
-- url     : https://prove2.me/theorems/30e39a08-1c2d-4aa2-b96d-e91d7715a245
-- title:
--   (3.37), p. 2288 — sufficient decrease φᵗ − φᵗ⁺¹ ≥ ‖xᵗ − xᵗ⁺¹‖²/(8c) + (α/2)‖Ax(yᵗ⁺¹, zᵗ) − b‖² + p‖zᵗ − zᵗ⁺¹‖²/(6β)
-- statement:
--   Suppose Assumption 2.2 holds with constant $L$, $\gamma$ satisfies (2.4), and $\Gamma>0$, $p>0$, $p>-\gamma$, $0<c<1/L_K$ with $L_K=L+p+\Gamma\sigma^2$ and $\sigma=\|A\|$. Let $x(y,z)$, $x^*(z)$, $d$, $M$ be as in (2.6)–(2.9) and let $\phi^t=K(x^t,z^t;y^t)-2d(y^t,z^t)+2M(z^t)$. Let $\alpha>0$ with
--   $$\alpha<\frac{\sigma_1^2}{4c\sigma^2},\qquad \sigma_1=c(p+\gamma),$$
--   and fix $y^0\in\mathbb R^m$. Then there is $\beta_0>0$ such that for every $\beta\in(0,1]$ with $\beta\le\beta_0$ and every run of Algorithm 2.2 with stepsizes $\alpha,\beta$ and initial dual vector $y^0$,
--   $$\phi^t-\phi^{t+1}\ \ge\ \frac1{8c}\|x^t-x^{t+1}\|^2+\frac\alpha2\|Ax(y^{t+1},z^t)-b\|^2+\frac p{6\beta}\|z^t-z^{t+1}\|^2\qquad\forall t\ge0.\tag{3.37}$$
--
--   This sufficient decrease of the potential is the core of the proof of Theorem 2.4: with (3.5) it makes all three residuals square-summable. The stepsize condition on $\alpha$ is the one the proof states before (3.25) ("if we choose $\alpha<\sigma_1^2/(4c\sigma^2)$").
--
--   **Formalization Note** The $\alpha$ condition is written $4c\sigma^2\alpha<\sigma_1^2$, which avoids dividing by $\sigma=\|A\|$ when $A=0$. The threshold $\beta_0$ (the paper's (3.27), built from $\beta'$, $D$, $\zeta$, $M$, $\Delta$, $\delta$, $\sigma_3$, $\sigma_5$) is existential because the paper does not compute it; it may depend on $\alpha$ and $y^0$ but not on $x^0$, $z^0$ or the run.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2288, (3.37), proof of Theorem 2.4 (α condition on p. 2286, β condition (3.27) on p. 2286)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem eq_3_37 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hA : Assumption22 f A b ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p c : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ α, 0 < α → 4 * c * ‖A‖ ^ 2 * α < (c * (p + γ)) ^ 2 → ∀ y0 : E m, ∃ β₀ > 0,
      ∀ β, 0 < β → β ≤ 1 → β ≤ β₀ → ∀ (x z : ℕ → E n) (y : ℕ → E m),
        IsRun f A b ℓ u Γ p c α β x y z → y 0 = y0 → ∀ t,
          phi f A b Γ p xs xst (x t) (z t) (y t) -
              phi f A b Γ p xs xst (x (t + 1)) (z (t + 1)) (y (t + 1)) ≥
            1 / (8 * c) * ‖x t - x (t + 1)‖ ^ 2 + α / 2 * ‖A (xs (y (t + 1)) (z t)) - b‖ ^ 2
              + p / (6 * β) * ‖z t - z (t + 1)‖ ^ 2 := by sorry

end ProxADMMLC.Conv
