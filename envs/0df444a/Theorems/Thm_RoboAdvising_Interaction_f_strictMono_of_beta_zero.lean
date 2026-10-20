-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_f_strictMono_of_beta_zero
-- name    : RoboAdvising.Interaction.f_strictMono_of_beta_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:41.649882+00:00
-- url     : https://prove2.me/theorems/f0f0a86e-a368-4d47-a792-fba40b2ebda8
-- title:
--   Proof of Proposition 5.1, p. 46 — if β = 0 and pϵ > 0, f is strictly increasing on φ ≥ 1 and f(1) = 0
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon \in (0,1]$ and suppose the client has no behavioral bias, $\beta = 0$. Then the bracket $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$ of the approximate personalization measure is strictly increasing on $[1,\infty)$, and
--   $$f(1) = 0 .$$
--
--   This is the case "$\arg\min = 1$" of Proposition 5.1(ii): without behavioral bias, interacting at every period is optimal.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: if `β = 0` and `pϵ > 0`, then `f` is strictly increasing on
`φ ≥ 1` and `f(1) = 0`. -/
theorem f_strictMono_of_beta_zero (P : Params) (hS : P.Standing) (hβ : P.β = 0) (hpe : 0 < P.pe) :
    StrictMonoOn (fAux P) (Set.Ici 1) ∧ fAux P 1 = 0 := by sorry
end RoboAdvising.Interaction
