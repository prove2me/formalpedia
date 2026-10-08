-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_mc_error_eq_sum_td_errors
-- name    : SuttonBartoRL.BatchTD.mc_error_eq_sum_td_errors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:37:54.278946+00:00
-- url     : https://prove2.me/theorems/15974c79-896b-4f70-84f6-7ec4751880ec
-- title:
--   The Monte Carlo error is a sum of TD errors (6.6)
-- statement:
--   Let $S_0, R_1, \dots, R_T, S_T$ be an episode ending in the terminal state, let $\gamma \in [0, 1]$, and let $V$ be a value array with $V(\text{terminal}) = 0$ that does not change during the episode. Write $G_t$ for the return after time $t$ and $\delta_k = R_{k+1} + \gamma V(S_{k+1}) - V(S_k)$ for the TD errors of $V$. Then for every $0 \le t \le T$,
--
--   $$
--   G_t - V(S_t) = \sum_{k=t}^{T-1} \gamma^{k-t}\,\delta_k .
--   $$
--
--   The identity relates the Monte Carlo target of (6.1) to the TD target of (6.2): the Monte Carlo error is exactly the discounted accumulation of one-step TD errors when $V$ is held fixed. Its generalizations underlie $n$-step and eligibility-trace methods.
--
--   **Formalization Note** The case $t = T$ (both sides $0$) is included. The identity is algebraic and holds for every real $\gamma$; the hypothesis $0 \le \gamma \le 1$ is the book's standing assumption and is kept.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (6.6), p. 121

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes

namespace SuttonBartoRL.BatchTD

/-- Eq. (6.6), p. 121: if the array `V` does not change during the episode, the Monte Carlo error
`G_t − V(S_t)` is the discounted sum of the TD errors `Σ_{k=t}^{T−1} γ^{k−t} δ_k`, where
`V(terminal) = 0`. Stated for every time `t ≤ T` (at `t = T` both sides are `0`). -/
theorem mc_error_eq_sum_td_errors {X : Type} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (V : X → ℝ) (e : Episode X) (t : ℕ) (ht : t ≤ e.length) :
    ret γ e t - extV V (stateAt e t) =
      ∑ k ∈ Finset.Ico t e.length, γ ^ (k - t) * tdError γ V e k := by sorry

end SuttonBartoRL.BatchTD
