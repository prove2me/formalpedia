-- Prove2me | Theorems.Thm_SuttonBartoRL_NStep_sarsaReturn_eq_sum_tdError
-- name    : SuttonBartoRL.NStep.sarsaReturn_eq_sum_tdError
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:58:19.886153+00:00
-- url     : https://prove2.me/theorems/a971c3b7-69f4-4741-829c-0fa2b11ba506
-- title:
--   The $n$-step Sarsa return in terms of a novel TD error (Exercise 7.4, Eq. (7.6))
-- statement:
--   Consider an episode $S_0, A_0, R_1, S_1, A_1, \dots, R_T, S_T$ that terminates at time $T$, a discount factor $\gamma$, and action-value estimates $Q_k$, one for each time $k \in \mathbb Z$ ($Q_{-1}$ being the initial estimate), which may change from step to step. Assume the terminal state has action value $0$ at every time: $Q_k(S_T, a) = 0$ for all $k$ and $a$. Let $G_{t:t+n}$ be the $n$-step Sarsa return (7.4),
--   $$G_{t:t+n} = R_{t+1} + \gamma R_{t+2} + \cdots + \gamma^{n-1} R_{t+n} + \gamma^n Q_{t+n-1}(S_{t+n}, A_{t+n}) \quad (t + n < T),$$
--   with $G_{t:t+n} = G_t$ if $t + n \ge T$. Then for every $n \ge 1$ and $0 \le t < T$,
--   $$G_{t:t+n} = Q_{t-1}(S_t, A_t) + \sum_{k=t}^{\min(t+n,\,T)-1} \gamma^{k-t}\,\big[R_{k+1} + \gamma Q_k(S_{k+1}, A_{k+1}) - Q_{k-1}(S_k, A_k)\big].$$
--
--   Unlike the state-value identity of Exercise 7.1, this one is exact even though the estimates change during the episode, because each bracket uses the estimate current at its own time.
--
--   **Formalization Note** The book poses this as Exercise 7.4 and gives no solution. The estimates are indexed by integers so that $Q_{t-1}$ at $t = 0$ is the initial estimate $Q_{-1}$. The hypothesis on $Q_k(S_T, \cdot)$ is the book's convention that terminal action values are zero; it is used only when $t + n \ge T$, where the telescoping sum ends in $\gamma^{T-t} Q_{T-1}(S_T, A_T)$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 7.4 and Eq. (7.6), p. 148 (with (7.4), p. 146)

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

namespace SuttonBartoRL.NStep

/-- Sutton & Barto (2018), Exercise 7.4 and (7.6), p. 148: the `n`-step Sarsa return (7.4) can be
written exactly in terms of a novel TD error,
`G_{t:t+n} = Q_{t−1}(S_t, A_t) + Σ_{k=t}^{min(t+n,T)−1} γ^{k−t} [R_{k+1} + γ Q_k(S_{k+1}, A_{k+1}) − Q_{k−1}(S_k, A_k)]`,
for `n ≥ 1` and `0 ≤ t < T`, where the action-value estimates `Q_k` may change from step to step and
the terminal state has action value zero at every time (`Q_k(S_T, a) = 0`). -/
theorem sarsaReturn_eq_sum_tdError {S A : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S)
    (At : ℕ → A) (T : ℕ) (Q : ℤ → S → A → ℝ) (hterm : ∀ (k : ℤ) (a : A), Q k (St T) a = 0)
    (t n : ℕ) (hn : 1 ≤ n) (ht : t < T) :
    sarsaReturn γ R St At T Q t n =
      Q ((t : ℤ) - 1) (St t) (At t) +
        ∑ k ∈ Finset.Ico t (min (t + n) T), γ ^ (k - t) * sarsaTDError γ R St At Q k := by sorry

end SuttonBartoRL.NStep
