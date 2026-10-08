-- Prove2me | Theorems.Thm_SuttonBartoRL_NStep_nStepError_eq_sum_tdError
-- name    : SuttonBartoRL.NStep.nStepError_eq_sum_tdError
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:58:12.022355+00:00
-- url     : https://prove2.me/theorems/a0f03d8a-71f9-4871-90b6-1cee2ad47bc6
-- title:
--   The $n$-step error is a discounted sum of TD errors (Exercise 7.1)
-- statement:
--   Consider an episode $S_0, R_1, S_1, \dots, R_T, S_T$ that terminates at time $T$, a discount factor $\gamma$, and a state-value estimate $V$ that does not change during the episode, with value $0$ at the terminal state: $V(S_T) = 0$. Let $G_{t:t+n}$ be the $n$-step return (7.1) (the complete return $G_t$ when $t + n \ge T$) and $\delta_k = R_{k+1} + \gamma V(S_{k+1}) - V(S_k)$ the TD error (6.5). Then for every $n \ge 1$ and $0 \le t < T$,
--   $$G_{t:t+n} - V(S_t) = \sum_{k=t}^{\min(t+n,\,T)-1} \gamma^{k-t}\, \delta_k.$$
--
--   This generalizes the identity (6.6) for the Monte Carlo error, which is the case $t + n \ge T$. It expresses the error used in the $n$-step TD update (7.2) through one-step TD errors.
--
--   **Formalization Note** The book poses this as Exercise 7.1 and gives no solution; the displayed identity is the standard answer. The hypothesis $V(S_T) = 0$ is the book's convention that terminal states have value zero.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 7.1, p. 143 (with (6.5)–(6.6), p. 121, and (7.1)–(7.2), p. 143)

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

namespace SuttonBartoRL.NStep

/-- Sutton & Barto (2018), Exercise 7.1, p. 143: if the value estimate `V` does not change during
the episode and the terminal state has value zero (`V(S_T) = 0`), the `n`-step error used in (7.2)
is a discounted sum of TD errors (6.5), generalizing (6.6):
`G_{t:t+n} − V(S_t) = Σ_{k=t}^{min(t+n,T)−1} γ^{k−t} δ_k`, for `n ≥ 1` and `0 ≤ t < T`. -/
theorem nStepError_eq_sum_tdError {S : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (T : ℕ)
    (V : S → ℝ) (hterm : V (St T) = 0) (t n : ℕ) (hn : 1 ≤ n) (ht : t < T) :
    nStepReturn γ R St T V t (t + n) - V (St t) =
      ∑ k ∈ Finset.Ico t (min (t + n) T), γ ^ (k - t) * tdError γ R St V k := by sorry

end SuttonBartoRL.NStep
