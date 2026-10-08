-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_lms_weights_closed_form
-- name    : SuttonBartoRL.Traces.lms_weights_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:37.957635+00:00
-- url     : https://prove2.me/theorems/77465b09-561c-4898-95b9-eaf8fb2efaed
-- title:
--   Eq. (12.14), first line: $w_T = F_{T-1}\cdots F_0 w_0 + \alpha G \sum_{k} F_{T-1}\cdots F_{k+1} x_k$
-- statement:
--   Let $w_0, \dots, w_T$ be the weights of the linear Monte Carlo (LMS) algorithm (12.13) over an episode of length $T \ge 1$, with step size $\alpha$, final return $G$ and features $x_0, \dots, x_{T-1} \in \mathbb R^d$, and let $F_t = I - \alpha x_t x_t^\top$. Then
--   $$
--   w_T = F_{T-1} F_{T-2} \cdots F_0\, w_0 + \alpha G \sum_{k=0}^{T-1} F_{T-1} F_{T-2} \cdots F_{k+1}\, x_k ,
--   $$
--   where the product in the $k = T - 1$ term is empty (the identity).
--
--   The first summand does not depend on $G$ and the second is $G$ times a vector that does not depend on $G$. This separation is what lets the backward view accumulate both parts during the episode.
--
--   **Formalization Note** The ordered products are `fadeProd α x j t` $= F_t \cdots F_j$. The identity holds for all real $\alpha$ and $G$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (12.14), first equality (the line with the braces), p. 302

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

namespace SuttonBartoRL.Traces

open Matrix

/-- Sutton & Barto, (12.14), p. 302, first equality: after the `T ≥ 1` forward-view updates (12.13),
`w_T = F_{T−1} ⋯ F_0 w_0 + α G Σ_{k=0}^{T−1} F_{T−1} ⋯ F_{k+1} x_k`. -/
theorem lms_weights_closed_form {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ)
    (T : ℕ) (hT : 1 ≤ T) :
    lmsWeights α G x w₀ T =
      fadeProd α x 0 (T - 1) *ᵥ w₀ +
        (α * G) • ∑ k ∈ Finset.range T, fadeProd α x (k + 1) (T - 1) *ᵥ x k := by sorry

end SuttonBartoRL.Traces
