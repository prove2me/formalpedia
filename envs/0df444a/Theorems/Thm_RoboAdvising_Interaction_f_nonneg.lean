-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_f_nonneg
-- name    : RoboAdvising.Interaction.f_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:42.301929+00:00
-- url     : https://prove2.me/theorems/2e381341-4f8c-44b0-9c3a-687f1e02a529
-- title:
--   Proof of Proposition 5.1, p. 46 — f ≥ 0 on φ ≥ 1, and f ≡ 0 if pϵ = 0 and β = 0
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon\in[0,1]$ and $\beta\ge0$, and let
--   $$f(\phi) = \frac{\beta\sigma_0}{\sqrt{\phi}}\Big(1-\frac{\phi-1}{2}p_\epsilon\Big) + \sqrt{\frac{\beta^2\sigma_0^2}{\phi}+\sigma_\epsilon^2}\;\frac{\phi-1}{2}p_\epsilon$$
--   be the bracket of the approximate personalization measure, $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$. Then
--
--   1. $f(\phi) \ge 0$ for every $\phi \ge 1$;
--   2. if $p_\epsilon = 0$ and $\beta = 0$, then $f \equiv 0$.
--
--   This is the first observation of the proof of Proposition 5.1(ii): $\widetilde{\mathcal R}$ is a non-negative measure, and in the degenerate case $\beta = p_\epsilon = 0$, excluded by the proposition, it does not depend on $\phi$.
--
--   **Formalization Note** Part 2 is stated for every real $\phi$; it holds there because every term carries a factor $\beta$ or $p_\epsilon$.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: `f ≥ 0` on `φ ≥ 1`, and `f ≡ 0` when `pϵ = 0` and `β = 0`. -/
theorem f_nonneg (P : Params) (hS : P.Standing) :
    (∀ φ : ℝ, 1 ≤ φ → 0 ≤ fAux P φ) ∧
    (P.pe = 0 → P.β = 0 → ∀ φ : ℝ, fAux P φ = 0) := by sorry
end RoboAdvising.Interaction
