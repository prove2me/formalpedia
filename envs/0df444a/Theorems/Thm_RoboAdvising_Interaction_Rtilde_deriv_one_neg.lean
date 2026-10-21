-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_Rtilde_deriv_one_neg
-- name    : RoboAdvising.Interaction.Rtilde_deriv_one_neg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:41.289953+00:00
-- url     : https://prove2.me/theorems/6bddf2af-31d3-48e3-a13a-2278d2373c05
-- title:
--   §5.2, p. 22 — pϵσϵ/(βσ0) < 1 implies ∂R̃(φ, β)/∂φ at φ = 1 is negative
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon\in[0,1]$ and $\beta>0$. If
--   $$\frac{p_\epsilon\sigma_\epsilon}{\beta\sigma_0} < 1,$$
--   then the approximate personalization measure $\phi \mapsto \widetilde{\mathcal R}(\phi,\beta)$ is differentiable at $\phi = 1$ and
--   $$\frac{\partial\widetilde{\mathcal R}(\phi,\beta)}{\partial\phi}\Big|_{\phi=1} < 0 .$$
--
--   This is a sufficient condition for when it is optimal not to interact with the client at every period: the idiosyncratic risk-aversion component, measured by $p_\epsilon\sigma_\epsilon$, is small compared with the behavioral bias $\beta\sigma_0$.
--
--   **Formalization Note** The case $p_\epsilon = 0$ is included, as on the page.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 22, §5.2 (display after (5.6))

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- §5.2, p. 22: for `β > 0`, `pϵσϵ/(βσ0) < 1` implies `∂R̃(φ, β)/∂φ` at `φ = 1` is negative. -/
theorem Rtilde_deriv_one_neg (P : Params) (hS : P.Standing) (hβ : 0 < P.β)
    (h : P.pe * P.se / (P.β * P.sig0) < 1) :
    ∃ d : ℝ, HasDerivAt (Rtilde P) d 1 ∧ d < 0 := by sorry
end RoboAdvising.Interaction
