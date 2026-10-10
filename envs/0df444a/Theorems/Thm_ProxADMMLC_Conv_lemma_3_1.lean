-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_1
-- name    : ProxADMMLC.Conv.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:47.861095+00:00
-- url     : https://prove2.me/theorems/aa6ad394-ef20-43bf-af70-11e62bb775cf
-- title:
--   Lemma 3.1 (primal descent), p. 2278 — K decreases by ‖xᵗ − xᵗ⁺¹‖²/(2c) + p‖zᵗ − zᵗ⁺¹‖²/(2β) − α‖Axᵗ − b‖²
-- statement:
--   Let $f$ satisfy Assumption 2.2(c) with constant $L>0$, let $\Gamma>0$, $p>0$, $0<\beta\le1$ and $0<c<1/L_K$ with $L_K=L+p+\Gamma\sigma^2$, $\sigma=\|A\|$, and let $\alpha$ be any real number. For every run $(x^t,y^t,z^t)$ of Algorithm 2.2 and every $t$,
--   $$K(x^t,z^t;y^t)-K(x^{t+1},z^{t+1};y^{t+1})\ \ge\ \frac1{2c}\|x^t-x^{t+1}\|^2+\frac p{2\beta}\|z^t-z^{t+1}\|^2-\alpha\|Ax^t-b\|^2.$$
--
--   This is the first of the three descent lemmas: the primal and proximal steps decrease $K$, and only the dual step can increase it.
--
--   **Formalization Note** Only Assumption 2.2(c) is assumed: (a), (b) and (2.4) are not used by this lemma.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2278, Lemma 3.1

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_1 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L)
    (Γ p c α β : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (x z : ℕ → E n) (y : ℕ → E m) (hrun : IsRun f A b ℓ u Γ p c α β x y z) :
    ∀ t, K f A b Γ p (x t) (z t) (y t) - K f A b Γ p (x (t + 1)) (z (t + 1)) (y (t + 1)) ≥
      1 / (2 * c) * ‖x t - x (t + 1)‖ ^ 2 + p / (2 * β) * ‖z t - z (t + 1)‖ ^ 2
        - α * ‖A (x t) - b‖ ^ 2 := by sorry

end ProxADMMLC.Conv
