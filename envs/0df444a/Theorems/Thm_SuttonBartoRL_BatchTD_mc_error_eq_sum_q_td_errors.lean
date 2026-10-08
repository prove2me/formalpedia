-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_mc_error_eq_sum_q_td_errors
-- name    : SuttonBartoRL.BatchTD.mc_error_eq_sum_q_td_errors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:38:23.744513+00:00
-- url     : https://prove2.me/theorems/380e4b31-959c-4424-87b3-62417ea2e3b1
-- title:
--   Action-value version of (6.6) (Exercise 6.8)
-- statement:
--   Let $S_0, A_0, R_1, S_1, A_1, \dots, S_{T-1}, A_{T-1}, R_T, S_T$ be an episode of state–action pairs ending in the terminal state, let $\gamma \in [0, 1]$, and let $Q$ be an action-value array with $Q(\text{terminal}, \cdot) = 0$ that does not change from step to step. With the action-value TD errors $\delta_k = R_{k+1} + \gamma Q(S_{k+1}, A_{k+1}) - Q(S_k, A_k)$, for every $0 \le t \le T$,
--
--   $$
--   G_t - Q(S_t, A_t) = \sum_{k=t}^{T-1} \gamma^{k-t}\,\delta_k .
--   $$
--
--   This is the identity behind Sarsa (6.7), whose TD error is exactly this $\delta_t$.
--
--   **Formalization Note** The book leaves this as an exercise without a solution. $Q(\text{terminal}, \cdot) = 0$ is the convention stated with (6.7) on the same page. The case $t = T$ is included; $0 \le \gamma \le 1$ is the standing assumption.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 6.8, p. 129

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes

namespace SuttonBartoRL.BatchTD

/-- Exercise 6.8, p. 129: the action-value version of (6.6). For an episode of state–action pairs
and a fixed array `Q` with `Q(terminal, ·) = 0`,
`G_t − Q(S_t, A_t) = Σ_{k=t}^{T−1} γ^{k−t} δ_k` with `δ_k = R_{k+1} + γ Q(S_{k+1}, A_{k+1}) − Q(S_k, A_k)`. -/
theorem mc_error_eq_sum_q_td_errors {S A : Type} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (Q : S → A → ℝ) (e : Episode (S × A)) (t : ℕ) (ht : t ≤ e.length) :
    ret γ e t - extQ Q (stateAt e t) =
      ∑ k ∈ Finset.Ico t e.length, γ ^ (k - t) * qTdError γ Q e k := by sorry

end SuttonBartoRL.BatchTD
