-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_average_reward_of_ergodic
-- name    : SuttonBartoRL.AverageReward.average_reward_of_ergodic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:01:48.205992+00:00
-- url     : https://prove2.me/theorems/27c528d2-25f4-43c5-817c-91cb7ba73f78
-- title:
--   (10.6)–(10.7): with a steady-state distribution, the average reward is $\sum_s \mu_\pi(s)\sum_a\pi(a|s)\sum_{s',r}p(s',r|s,a)r$
-- statement:
--   Let $\pi$ be a policy in a finite MDP, and suppose the **steady-state distribution** exists and is independent of the initial state: there is $\mu$ with
--   $$
--   \lim_{t\to\infty} \Pr\{S_t = s \mid S_0 = s_0,\ A_{0:t-1}\sim\pi\} = \mu(s) \quad\text{for all } s_0, s .
--   $$
--   Then from every initial state $s_0$ both limits in the definition of the average reward exist and equal the $\mu$-average of the expected one-step reward:
--   $$
--   \lim_{t\to\infty} \mathbb E[R_t \mid S_0 = s_0, A_{0:t-1}\sim\pi] \;=\; \lim_{h\to\infty}\frac1h\sum_{t=1}^{h} \mathbb E[R_t \mid S_0 = s_0, A_{0:t-1}\sim\pi] \;=\; \sum_s \mu(s)\sum_a \pi(a\mid s)\sum_{s', r} p(s', r\mid s, a)\, r .
--   $$
--
--   This is the sense in which (10.6), (10.7) and the formula in the last line of (10.7) agree for an ergodic MDP. It connects the definition of the average reward $r(\pi)$ as a long-run rate (10.6) to the closed form used in the rest of the chapter.
--
--   **Formalization Note** $\Pr\{S_t = s\mid S_0 = s_0\}$ is $(P_\pi^t)(s_0, s)$ and $\mathbb E[R_{t+1}\mid S_0=s_0]$ is $(P_\pi^t r_\pi)(s_0)$, so the sum over $t < h$ in Lean is the book's sum over $t = 1,\dots,h$. The book's hypothesis "the MDP is ergodic" is encoded as exactly the condition the text gives for it: the limit $\mu$ exists and does not depend on $S_0$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (10.6)–(10.7) and the following paragraph, p. 249

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

open Filter Topology

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), (10.6)–(10.7), p. 249: if the steady-state distribution
`μ(s) = lim_{t→∞} Pr{S_t = s | A_{0:t-1} ∼ π}` exists and is independent of `S_0`, then from every
initial state `s₀` the limit (10.7) `lim_{t→∞} E[R_t | S_0 = s₀, A_{0:t-1} ∼ π]` exists and equals
`Σ_s μ(s) Σ_a π(a | s) Σ_{s', r} p(s', r | s, a) r`, and so does the Cesàro limit (10.6)
`lim_{h→∞} (1/h) Σ_{t=1}^{h} E[R_t | S_0 = s₀, A_{0:t-1} ∼ π]`.
(`expectedRewardAt M π t s₀` is `E[R_{t+1} | S_0 = s₀]`, so the sum over `t < h` is the book's
sum over `t = 1, …, h`.) -/
theorem average_reward_of_ergodic {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (hμ : ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s)))
    (s₀ : S) :
    Tendsto (fun t : ℕ => M.expectedRewardAt π t s₀) atTop (𝓝 (avgReward M π μ)) ∧
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, M.expectedRewardAt π t s₀)
      atTop (𝓝 (avgReward M π μ)) := by sorry

end SuttonBartoRL.AverageReward
