-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_lms_step_fading_form
-- name    : SuttonBartoRL.Traces.lms_step_fading_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:35.330984+00:00
-- url     : https://prove2.me/theorems/d38b6d2d-7eb6-44be-abc7-96e401ef12ed
-- title:
--   One LMS update as a fading matrix: $w_{t+1} = F_t w_t + \alpha G x_t$
-- statement:
--   Let $w_0, w_1, \dots$ be the weights of the linear Monte Carlo (LMS) algorithm (12.13) with step size $\alpha$, final return $G$ and feature vectors $x_t \in \mathbb R^d$, and let $F_t = I - \alpha x_t x_t^\top$ be the fading matrix. Then for every $t$,
--   $$
--   w_{t+1} = F_t\, w_t + \alpha G\, x_t .
--   $$
--
--   This splits each update into a part that forgets the current weights along $x_t$ and a part that uses the return. Unrolling it gives the closed form (12.14).
--
--   **Formalization Note** The identity holds for all real $\alpha$ and $G$; the book's step size is positive, and no sign condition is needed. It is stated for every $t \in \mathbb N$ (the book writes it at $t = T - 1$).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §12.6, first display on p. 302 (from Eq. (12.13), p. 301)

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

namespace SuttonBartoRL.Traces

open Matrix

/-- Sutton & Barto, §12.6, p. 302, first display: each forward-view (LMS) update (12.13) is
`w_{t+1} = F_t w_t + α G x_t` with the fading matrix `F_t = I − α x_t x_tᵀ`. -/
theorem lms_step_fading_form {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (t : ℕ) :
    lmsWeights α G x w₀ (t + 1) =
      fadingMatrix α x t *ᵥ lmsWeights α G x w₀ t + (α * G) • x t := by sorry

end SuttonBartoRL.Traces
