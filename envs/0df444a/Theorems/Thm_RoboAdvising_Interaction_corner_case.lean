-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_corner_case
-- name    : RoboAdvising.Interaction.corner_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:40.263073+00:00
-- url     : https://prove2.me/theorems/56073890-0d70-482e-8e62-1e9997301529
-- title:
--   Proof of Proposition 5.1, p. 46 — g′(φ) ≥ ½φ^{−1/2}g(1); if g(1) ≥ 0, then f′ ≥ 0 on φ ≥ 1 and f is minimized at φ = 1
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon\in(0,1]$ and $\beta>0$, and let $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$ and $g$ be the functions of the proof of Proposition 5.1, with $f'(\phi) = \tfrac12\frac{\beta\sigma_0p_\epsilon}{\phi^2}g(\phi)$. Then:
--
--   1. for every $\phi \ge 1$, $g$ is differentiable at $\phi$ and
--   $$g'(\phi) \ge \frac12\,\phi^{-1/2}\,g(1);$$
--   2. if $g(1) \ge 0$, then $f$ is differentiable with $f'(\phi) \ge 0$ at every $\phi \ge 1$, and $f$ attains its minimum over $[1,\infty)$ at $\phi = 1$.
--
--   This is the corner case of Proposition 5.1(ii) with $\beta > 0$, $p_\epsilon > 0$: when the idiosyncratic shocks dominate, interacting at every period is optimal.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1 (display of g′(φ) and the sentence after it)

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: for `β > 0`, `pϵ > 0`, `g′(φ) ≥ ½ φ^{−1/2} g(1)` for all
`φ ≥ 1`; hence if `g(1) ≥ 0`, then `f′(φ) ≥ 0` for all `φ ≥ 1` and `f` is minimized at `φ = 1`. -/
theorem corner_case (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe) :
    (∀ φ : ℝ, 1 ≤ φ → ∃ d : ℝ, HasDerivAt (gAux P) d φ ∧
        1 / 2 * (1 / Real.sqrt φ) * gAux P 1 ≤ d) ∧
    (0 ≤ gAux P 1 →
      (∀ φ : ℝ, 1 ≤ φ → ∃ d : ℝ, HasDerivAt (fAux P) d φ ∧ 0 ≤ d) ∧
      IsMinOn (fAux P) (Set.Ici 1) 1) := by sorry
end RoboAdvising.Interaction
