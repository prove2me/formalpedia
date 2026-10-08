-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_aux_vector_closed_form
-- name    : SuttonBartoRL.Traces.aux_vector_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:58.850348+00:00
-- url     : https://prove2.me/theorems/d2e9d15f-6f0a-4f08-a063-e0f9d846f908
-- title:
--   The auxiliary vector $a_t = a_{t-1} - \alpha x_t x_t^\top a_{t-1}$ equals $F_t \cdots F_0 w_0$ (corrected)
-- statement:
--   Let $x_0, x_1, \dots \in \mathbb R^d$ be feature vectors, $\alpha$ a step size, $w_0 \in \mathbb R^d$, and $F_t = I - \alpha x_t x_t^\top$. Compute the auxiliary vector by
--   $$
--   a_0 = w_0 - \alpha x_0 x_0^\top w_0, \qquad a_t = a_{t-1} - \alpha x_t x_t^\top a_{t-1} \quad (t \ge 1).
--   $$
--   Then for every $t \ge 0$,
--   $$
--   a_t = F_t F_{t-1} \cdots F_0\, w_0 .
--   $$
--
--   This is the part of (12.14) that does not involve the return. It too is computed in $O(d)$ per step.
--
--   **Formalization Note** This is the **corrected** statement. The book initializes $a_0 = w_0$, which contradicts the identity at $t = 0$ whenever $\alpha x_0^\top w_0\, x_0 \neq 0$: with $d = 1$, $x_0 = 1$, $\alpha = 1/2$, $w_0 = 1$ one has $F_0 w_0 = 1/2 \neq 1$. With $a_0 = F_0 w_0$ (the same recursion started from $a_{-1} = w_0$) the book's definition $a_t \doteq F_t \cdots F_0 w_0$ and its recursion agree for all $t$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §12.6, the auxiliary vector a_t, last display of p. 302 (initialization a_0 = w_0 corrected to a_0 = F_0 w_0)

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

namespace SuttonBartoRL.Traces

open Matrix

/-- Sutton & Barto, §12.6, p. 302 (corrected): the incrementally computed auxiliary vector
(`a_0 = F_0 w_0`, `a_t = a_{t−1} − α x_t x_tᵀ a_{t−1}`) equals `F_t F_{t−1} ⋯ F_0 w_0`.
The book prints the initialization `a_0 = w_0`, which contradicts this identity at `t = 0`. -/
theorem aux_vector_closed_form {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (t : ℕ) :
    auxVec α x w₀ t = fadeProd α x 0 t *ᵥ w₀ := by sorry

end SuttonBartoRL.Traces
