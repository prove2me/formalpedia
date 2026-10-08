-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_exercise_10_6
-- name    : SuttonBartoRL.AverageReward.exercise_10_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:01:23.719006+00:00
-- url     : https://prove2.me/theorems/51249534-3909-4546-bbd3-53510a9d197b
-- title:
--   Exercise 10.6: the rewards $+1,0,+1,0,\dots$ have average $1/2$ and differential values $\pm 1/4$
-- statement:
--   Consider a finite MDP and a policy $\pi$ under which the expected reward sequence starting from a state $\mathsf A$ is $+1, 0, +1, 0, \dots$ and starting from a state $\mathsf B$ is $0, +1, 0, +1, \dots$; that is, for all $t \ge 0$,
--   $$
--   \mathbb E_\pi[R_{t+1}\mid S_0 = \mathsf A] = \begin{cases}1 & t \text{ even}\\ 0 & t\text{ odd}\end{cases},\qquad
--   \mathbb E_\pi[R_{t+1}\mid S_0 = \mathsf B] = \begin{cases}0 & t \text{ even}\\ 1 & t\text{ odd.}\end{cases}
--   $$
--   Then:
--   1. the average reward (10.6) is $\lim_{h\to\infty}\frac1h\sum_{t=1}^h \mathbb E[R_t\mid S_0] = \tfrac12$ from both $\mathsf A$ and $\mathsf B$;
--   2. the limit (10.7) $\lim_{t\to\infty}\mathbb E[R_t\mid S_0]$ does not exist from $\mathsf A$ nor from $\mathsf B$;
--   3. there is no steady-state distribution: no $\mu$ with $\Pr\{S_t = s\mid S_0 = s_0\}\to\mu(s)$ for all $s_0, s$;
--   4. with $r(\pi) = \tfrac12$, the differential values (10.13) are
--   $$
--   v_\pi(\mathsf A) = \tfrac14, \qquad v_\pi(\mathsf B) = -\tfrac14 .
--   $$
--
--   The book leaves the answers to the reader; they are computed here. The example shows that the average reward (10.6) can be well defined when the MDP is not ergodic, and that (10.13) repairs the differential return (10.9), whose implicit limit does not exist here.
--
--   **Formalization Note** The book's "MDP that under any policy produces the deterministic sequence of rewards" is encoded by a hypothesis on the expected rewards of one policy, which is all the exercise uses; the statement therefore applies to every such MDP and policy. The differential value is the explicit two-limit statement of (10.13), with $\gamma \to 1$ from below.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Exercise 10.6 with Eq. (10.13), p. 251 (no solution printed)

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

open Filter Topology

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), Exercise 10.6, p. 251 (answers not printed; computed here). Suppose that,
under the policy `π`, the expected reward sequence from state `A` is `+1, 0, +1, 0, …` and from
state `B` is `0, +1, 0, +1, …`. Then
1. the average reward (10.6) is `1/2` from both states;
2. the limit (10.7) does not exist from either state;
3. there is no steady-state distribution independent of `S_0`;
4. the differential values (10.13) with `r(π) = 1/2` are `v_π(A) = 1/4` and `v_π(B) = −1/4`. -/
theorem exercise_10_6 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (sA sB : S)
    (hA : ∀ t : ℕ, M.expectedRewardAt π t sA = if Even t then 1 else 0)
    (hB : ∀ t : ℕ, M.expectedRewardAt π t sB = if Even t then 0 else 1) :
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, M.expectedRewardAt π t sA)
      atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun h : ℕ => (1 / (h : ℝ)) * ∑ t ∈ Finset.range h, M.expectedRewardAt π t sB)
      atTop (𝓝 (1 / 2)) ∧
    (¬ ∃ L : ℝ, Tendsto (fun t : ℕ => M.expectedRewardAt π t sA) atTop (𝓝 L)) ∧
    (¬ ∃ L : ℝ, Tendsto (fun t : ℕ => M.expectedRewardAt π t sB) atTop (𝓝 L)) ∧
    (¬ ∃ μ : S → ℝ, ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s))) ∧
    HasDifferentialValue M π (1 / 2) sA (1 / 4) ∧
    HasDifferentialValue M π (1 / 2) sB (-1 / 4) := by sorry

end SuttonBartoRL.AverageReward
