-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_hasDerivAt_f
-- name    : RoboAdvising.Interaction.hasDerivAt_f
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:43.188896+00:00
-- url     : https://prove2.me/theorems/5b4f7af1-9866-40b4-ae74-c66d79ec5337
-- title:
--   Proof of Proposition 5.1, p. 46 — f′(φ) = ½ (βσ0pϵ/φ²) g(φ)
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon\in(0,1]$ and $\beta>0$. Let $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$ be the bracket of the approximate personalization measure and
--   $$g(\phi) = -\frac{\sqrt{\phi}}{p_\epsilon} + \frac12\Big(1-\frac{1}{\sqrt{1+\frac{\sigma_\epsilon^2\phi}{\beta^2\sigma_0^2}}}\Big)\sqrt{\phi}(\phi-1) + \Big(\sqrt{1+\frac{\sigma_\epsilon^2\phi}{\beta^2\sigma_0^2}}-1\Big)\phi^{3/2}.$$
--   Then for every $\phi > 0$, $f$ is differentiable at $\phi$ and
--   $$f'(\phi) = \frac12\,\frac{\beta\sigma_0 p_\epsilon}{\phi^2}\,g(\phi).$$
--
--   The factorization reduces the sign of $f'$, and hence the location of the minimizer of $\widetilde{\mathcal R}$, to the sign of $g$.
--
--   **Formalization Note** The page writes the prefactor as $\beta\sigma_0 p/\phi^2$; $p$ is $p_\epsilon$.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1 (display of f′(φ))

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: for `β > 0`, `pϵ > 0` and `φ > 0`,
`f′(φ) = ½ (βσ0pϵ/φ²) g(φ)`. -/
theorem hasDerivAt_f (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (φ : ℝ) (hφ : 0 < φ) :
    HasDerivAt (fAux P) (1 / 2 * (P.β * P.sig0 * P.pe / φ ^ 2) * gAux P φ) φ := by sorry
end RoboAdvising.Interaction
