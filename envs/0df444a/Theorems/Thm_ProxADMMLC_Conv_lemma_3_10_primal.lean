-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_10_primal
-- name    : ProxADMMLC.Conv.lemma_3_10_primal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:58.618279+00:00
-- url     : https://prove2.me/theorems/96ab5135-928b-4c05-983d-bb7fbd47c93e
-- title:
--   Lemma 3.10 (3.10)–(3.11), p. 2282 — primal error bounds with σ₁ = c(p + γ), σ₂ = σ₁/(1 + σ₁)
-- statement:
--   Let $f$ satisfy Assumption 2.2(c) with constant $L$ and (2.4) with constant $\gamma$, let $\Gamma>0$, $p>0$, $p>-\gamma$, $0<\beta\le1$, and $0<c<1/L_K$ with $L_K=L+p+\Gamma\|A\|^2$. Let $x(y,z)$ be the minimizer (2.7) and $(x^t,y^t,z^t)$ any run of Algorithm 2.2. With
--   $$\sigma_1=c(p+\gamma),\qquad \sigma_2=\frac{\sigma_1}{1+\sigma_1},$$
--   for every $t$,
--   $$\|x^{t+1}-x^t\|\ \ge\ \sigma_1\,\|x^t-x(y^{t+1},z^t)\|,\qquad \|x^{t+1}-x^t\|\ \ge\ \sigma_2\,\|x^{t+1}-x(y^{t+1},z^t)\|.\tag{3.10–3.11}$$
--
--   These primal error bounds turn the step length of the projected-gradient update into a bound on the distance to the exact minimizer of $K(\cdot,z^t;y^{t+1})$; they enter the proof of (3.37) through (3.24).
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2282, Lemma 3.10, (3.10)–(3.11) (proof in Appendix C, p. 2301)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_10_primal {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L)
    (γ : ℝ) (hγ : MonoConst f ℓ u γ) (Γ p c α β : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    ∀ t, c * (p + γ) * ‖x t - xs (y (t + 1)) (z t)‖ ≤ ‖x (t + 1) - x t‖ ∧
      c * (p + γ) / (1 + c * (p + γ)) * ‖x (t + 1) - xs (y (t + 1)) (z t)‖ ≤
        ‖x (t + 1) - x t‖ := by sorry

end ProxADMMLC.Conv
