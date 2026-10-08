-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_w_to_2w_diverges
-- name    : SuttonBartoRL.OffPolicy.w_to_2w_diverges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:21:38.012048+00:00
-- url     : https://prove2.me/theorems/c01ca24f-1d2c-48f6-9a00-21c43d9dc6e2
-- title:
--   The w-to-2w example — off-policy semi-gradient TD(0) diverges for γ > 1/2
-- statement:
--   Consider two states whose estimated values are $w$ and $2w$ (scalar features $1$ and $2$). In the first state only one action is available, and it leads deterministically to the second state with reward $0$, so the importance-sampling ratio is $\rho_t = 1$. Apply the off-policy semi-gradient TD(0) update repeatedly to this one transition:
--   $$
--   \delta_t = 0 + \gamma\,2w_t - w_t,\qquad w_{t+1} = w_t + \alpha\,\rho_t\,\delta_t\,\nabla\hat v(S_t,w_t) = w_t + \alpha\cdot 1\cdot\delta_t\cdot 1 .
--   $$
--   Let $\alpha > 0$ and $\tfrac12 < \gamma \le 1$. Then
--
--   1. $w_{t+1} = \bigl(1 + \alpha(2\gamma - 1)\bigr)\,w_t$ for every $t$;
--   2. the factor $1 + \alpha(2\gamma-1)$ exceeds $1$;
--   3. if $w_0 > 0$ then $w_t \to +\infty$, and if $w_0 < 0$ then $w_t \to -\infty$.
--
--   The example isolates why off-policy training can diverge: the transition out of the $2w$ state, which would pull $w$ back, is never trained on.
--
--   **Formalization Note** The fragment is formalized as the scalar recursion it induces, with the numbers $0$ (reward), $1$ (ratio and gradient), $1$ and $2$ (features) written literally. The discount range $\gamma\le 1$ is the book's standing assumption.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §11.2, the w-to-2w example, p. 260

import Mathlib

open Filter

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), §11.2, p. 260: the w-to-2w example. Two states with scalar features
`x = 1` and `x = 2` (estimated values `w` and `2w`); the only action in the first state moves
deterministically to the second with reward `0`, so `ρ_t = 1`. Repeating off-policy semi-gradient
TD(0) (11.2) on that one transition,
`w_{t+1} = w_t + α ρ_t δ_t ∇v̂(S_t, w_t)` with `δ_t = 0 + γ·2w_t − w_t` and `∇v̂(S_t, w_t) = 1`,
multiplies `w` by `1 + α(2γ − 1)`, which exceeds `1` whenever `γ > 1/2`, for every `α > 0`;
`w_t` then goes to `+∞` or `−∞` according to the sign of `w_0`. -/
theorem w_to_2w_diverges (α γ : ℝ) (hα : 0 < α) (hγ : 1 / 2 < γ) (hγ1 : γ ≤ 1)
    (w : ℕ → ℝ)
    (hupd : ∀ t, w (t + 1) = w t + α * 1 * (0 + γ * (2 * w t) - 1 * w t) * 1) :
    (∀ t, w (t + 1) = (1 + α * (2 * γ - 1)) * w t) ∧
    1 < 1 + α * (2 * γ - 1) ∧
    (0 < w 0 → Tendsto w atTop atTop) ∧
    (w 0 < 0 → Tendsto w atTop atBot) := by sorry

end SuttonBartoRL.OffPolicy
