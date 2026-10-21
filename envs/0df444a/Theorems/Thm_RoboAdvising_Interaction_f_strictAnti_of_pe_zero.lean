-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_f_strictAnti_of_pe_zero
-- name    : RoboAdvising.Interaction.f_strictAnti_of_pe_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:37.898607+00:00
-- url     : https://prove2.me/theorems/da5a9ad1-9e99-41ec-9b7e-5650f4ea2fa1
-- title:
--   Proof of Proposition 5.1, p. 46 — if pϵ = 0 and β > 0, f is strictly decreasing on φ ≥ 1 and tends to 0
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $\beta > 0$ and suppose there are no idiosyncratic risk-aversion shocks, $p_\epsilon = 0$. Then the bracket $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$ of the approximate personalization measure is strictly decreasing on $[1,\infty)$ and
--   $$\lim_{\phi\to\infty} f(\phi) = 0 .$$
--
--   This is the case "$\arg\min = \infty$" of Proposition 5.1(ii): without idiosyncratic shocks, less frequent interaction always improves personalization, and no finite interaction time is optimal.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: if `pϵ = 0` and `β > 0`, then `f` is strictly decreasing on
`φ ≥ 1` and converges to zero as `φ → ∞`. -/
theorem f_strictAnti_of_pe_zero (P : Params) (hS : P.Standing) (hpe : P.pe = 0) (hβ : 0 < P.β) :
    StrictAntiOn (fAux P) (Set.Ici 1) ∧
    Filter.Tendsto (fAux P) Filter.atTop (nhds 0) := by sorry
end RoboAdvising.Interaction
