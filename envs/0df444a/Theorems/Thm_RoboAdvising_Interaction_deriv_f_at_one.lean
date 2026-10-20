-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_deriv_f_at_one
-- name    : RoboAdvising.Interaction.deriv_f_at_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:55.149986+00:00
-- url     : https://prove2.me/theorems/cbb0eb71-0f24-477c-b091-53e051b8f513
-- title:
--   Proof of Proposition 5.1, p. 46 — f′(1) = ½βσ0pϵ(√(1 + σϵ²/(β²σ0²)) − 1 − 1/pϵ) ≥ 0 ⟺ pϵσϵ²/(β²σ0²) ≥ 2 + 1/pϵ
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon\in(0,1]$ and $\beta>0$, and let $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$ be the bracket of the approximate personalization measure. Then $f$ is differentiable at $\phi = 1$ with
--   $$f'(1) = \frac12\beta\sigma_0 p_\epsilon\left(\sqrt{1+\frac{\sigma_\epsilon^2}{\beta^2\sigma_0^2}} - 1 - \frac{1}{p_\epsilon}\right),$$
--   and
--   $$f'(1) \ge 0 \iff \frac{p_\epsilon\sigma_\epsilon^2}{\beta^2\sigma_0^2} \ge 2 + \frac{1}{p_\epsilon}.$$
--
--   The criterion says when interacting at every period is locally optimal: the idiosyncratic shock variance must dominate the behavioral bias.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1 (display of f′(1))

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: for `β > 0`, `pϵ > 0`,
`f′(1) = ½βσ0pϵ(√(1 + σϵ²/(β²σ0²)) − 1 − 1/pϵ)`, and `f′(1) ≥ 0` iff
`pϵσϵ²/(β²σ0²) ≥ 2 + 1/pϵ`. -/
theorem deriv_f_at_one (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) :
    HasDerivAt (fAux P)
      (1 / 2 * P.β * P.sig0 * P.pe *
        (Real.sqrt (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) - 1 - 1 / P.pe)) 1 ∧
    (0 ≤ 1 / 2 * P.β * P.sig0 * P.pe *
        (Real.sqrt (1 + P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) - 1 - 1 / P.pe) ↔
      2 + 1 / P.pe ≤ P.pe * P.se ^ 2 / (P.β ^ 2 * P.sig0 ^ 2)) := by sorry
end RoboAdvising.Interaction
