-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_dutch_trace_closed_form
-- name    : SuttonBartoRL.Traces.dutch_trace_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:45.129807+00:00
-- url     : https://prove2.me/theorems/75e020b1-f0c2-46f6-bad8-9e4ff3747e7a
-- title:
--   The dutch trace $z_t = z_{t-1} + (1-\alpha z_{t-1}^\top x_t)x_t$ equals $\sum_{k\le t} F_t\cdots F_{k+1} x_k$
-- statement:
--   Let $x_0, x_1, \dots \in \mathbb R^d$ be feature vectors, $\alpha$ a step size, $F_t = I - \alpha x_t x_t^\top$, and let the dutch trace be computed by $z_0 = x_0$ and
--   $$
--   z_t = z_{t-1} + (1 - \alpha z_{t-1}^\top x_t)\, x_t \qquad (t \ge 1).
--   $$
--   Then for every $t \ge 0$,
--   $$
--   z_t = \sum_{k=0}^{t} F_t F_{t-1} \cdots F_{k+1}\, x_k .
--   $$
--
--   So the $O(d)$ recursion produces exactly the vector that multiplies $\alpha G$ in (12.14). It is the dutch trace (12.11) in the case $\gamma\lambda = 1$.
--
--   **Formalization Note** The book states the identity for $1 \le t < T$; here it is stated for every $t$, including $t = 0$ (where both sides are $x_0$), since the episode length plays no role in it.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §12.6, the derivation of the dutch trace z_t, p. 302

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

namespace SuttonBartoRL.Traces

open Matrix

/-- Sutton & Barto, §12.6, p. 302: the incrementally computed dutch trace
(`z_0 = x_0`, `z_t = z_{t−1} + (1 − α z_{t−1}ᵀ x_t) x_t`) equals `Σ_{k=0}^{t} F_t F_{t−1} ⋯ F_{k+1} x_k`. -/
theorem dutch_trace_closed_form {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    dutchTrace α x t = ∑ k ∈ Finset.range (t + 1), fadeProd α x (k + 1) t *ᵥ x k := by sorry

end SuttonBartoRL.Traces
