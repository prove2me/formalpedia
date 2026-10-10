-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_6
-- name    : ProxADMMLC.Conv.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:37.167806+00:00
-- url     : https://prove2.me/theorems/0725f041-19ac-49a3-bda8-f2962b3cf95d
-- title:
--   Lemma 3.6, p. 2281 — a fixed point (x, y, z) = (x⁺, y⁺, z⁺) of the iteration gives (x, y) ∈ W
-- statement:
--   Let $\alpha>0$, $\beta>0$, $c>0$, and let $\Gamma,p$ be any constants. Let $y^+$, $x^+$, $z^+$ be the updates (3.7)–(3.9) of Algorithm 2.2 from $(x,y,z)$:
--   $$y^+=y+\alpha(Ax-b),\qquad x^+=[x-c\nabla_xK(x,z;y^+)]_+,\qquad z^+=z+\beta(x^+-z).$$
--   If $(x,y,z)=(x^+,y^+,z^+)$, then $(x,y)\in W$: $x$ is a stationary point of (1.1) and $y$ a multiplier for its equality constraint.
--
--   The lemma says the algorithm can only stop at a KKT pair; Corollary 3.7 is its quantitative version.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2281, Lemma 3.6 with (3.7)–(3.9)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_6 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (Γ p c α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    ∀ (x z : E n) (y : E m), yPlus A b α x y = y → xPlus f A b ℓ u Γ p c α x z y = x →
      zPlus f A b ℓ u Γ p c α β x z y = z → (x, y) ∈ Wset f A b ℓ u := by sorry

end ProxADMMLC.Conv
