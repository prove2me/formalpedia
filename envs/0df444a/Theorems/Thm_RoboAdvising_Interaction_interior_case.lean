-- Prove2me | Theorems.Thm_RoboAdvising_Interaction_interior_case
-- name    : RoboAdvising.Interaction.interior_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:57.641461+00:00
-- url     : https://prove2.me/theorems/c92b80c5-5343-42ac-96a8-e1cdc08ed8f7
-- title:
--   Proof of Proposition 5.1, p. 46 — if g(1) < 0, g is strictly convex and → ∞, has a unique zero, and f is minimized there
-- statement:
--   Let $\sigma_0>0$, $\sigma_\epsilon>0$, $p_\epsilon\in(0,1]$ and $\beta>0$, and let $f = \sqrt{\pi/2}\,\widetilde{\mathcal R}$ and $g$ be the functions of the proof of Proposition 5.1. Suppose $g(1) < 0$ (equivalently $f'(1) < 0$). Then
--
--   1. $g$ is strictly convex on $[1,\infty)$;
--   2. $g(\phi) \to \infty$ as $\phi \to \infty$;
--   3. there is exactly one $\phi_0 \ge 1$ with $g(\phi_0) = 0$;
--   4. $f$ attains its minimum over $[1,\infty)$ at every $\phi_0 \ge 1$ with $g(\phi_0) = 0$.
--
--   This is the interior case of Proposition 5.1(ii): the optimal time between interactions is the unique root of $g$.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, p. 46, proof of Proposition 5.1

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Interaction


/-- Proof of Proposition 5.1, p. 46: for `β > 0`, `pϵ > 0` and `g(1) < 0`, `g` is strictly convex on
`φ ≥ 1` and `g(φ) → ∞`; hence `g` has a unique zero `φ0 ≥ 1`, and `f` is minimized there. -/
theorem interior_case (P : Params) (hS : P.Standing) (hβ : 0 < P.β) (hpe : 0 < P.pe)
    (hg : gAux P 1 < 0) :
    StrictConvexOn ℝ (Set.Ici 1) (gAux P) ∧
    Filter.Tendsto (gAux P) Filter.atTop Filter.atTop ∧
    (∃! φ0 : ℝ, 1 ≤ φ0 ∧ gAux P φ0 = 0) ∧
    (∀ φ0 : ℝ, 1 ≤ φ0 → gAux P φ0 = 0 → IsMinOn (fAux P) (Set.Ici 1) φ0) := by sorry
end RoboAdvising.Interaction
