-- Prove2me | Theorems.Thm_SuttonBartoRL_ImportanceSampling_per_decision_reward_term
-- name    : SuttonBartoRL.ImportanceSampling.per_decision_reward_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:50:36.490218+00:00
-- url     : https://prove2.me/theorems/63f0e051-b9df-4345-8ce3-6e096f4780df
-- title:
--   Later ratio factors drop out: $\mathbb E[\rho_{t:T-1}R_{t+k}] = \mathbb E[\rho_{t:t+k-1}R_{t+k}]$ (5.14)
-- statement:
--   Let $b$ cover $\pi$, start episodes at $S_0 = s$ and generate them with $b$, and assume that under $b$ every episode from $s$ terminates within $H$ steps with probability one. Then for every $k \ge 1$,
--
--   $$
--   \mathbb E_b\bigl[\rho_{0:T-1} R_k \mid S_0 = s\bigr] = \mathbb E_b\bigl[\rho_{0:k-1} R_k \mid S_0 = s\bigr],
--   $$
--
--   where $R_k$ is taken to be $0$ if the episode has terminated before time $k$. For $k = 1$ this is (5.14): only the first factor $\pi(A_0 \mid S_0)/b(A_0 \mid S_0)$ of the ratio matters for the first reward.
--
--   The identity is the key step towards per-decision importance sampling: the factors of the ratio for decisions made after a reward are irrelevant in expectation.
--
--   **Formalization Note** The book writes the identity for a general time $t$ with $\mathbb E$ over trajectories under $b$; here $t = 0$ and the expectation is conditional on $S_0 = s$ (the Markov property makes the two equivalent). The book does not state a termination assumption; the bounded-horizon hypothesis ($\Pr_b\{T \le H \mid S_0 = s\} = 1$) makes every expectation a finite sum and is a restriction relative to the book's episodic setting.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.9, Eq. (5.14) and the k-th sub-term display, p. 114; Exercise 5.13, p. 115

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes

namespace SuttonBartoRL.ImportanceSampling

/-- Sutton & Barto (2018), §5.9, p. 114, Eq. (5.14) (`k = 1`) and its `k`-th form:
`E_b[ρ_{t:T-1} R_{t+k}] = E_b[ρ_{t:t+k-1} R_{t+k}]`, with `t = 0` and `S_0 = s`, where the reward
`R_k` is `0` if the episode has terminated before time `k`. Hypotheses: coverage, and termination of
every episode from `s` under `b` within `H` steps with probability one. -/
theorem per_decision_reward_term {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (hcov : Coverage π b) (s : S) (H : ℕ)
    (hH : ∑ n ∈ Finset.range (H + 1), ∑ e : Episode M n, episodeProb M term b s e = 1)
    (k : ℕ) (hk : 1 ≤ k) :
    expectation M term b s (fun n e => e.isRatio π b n * e.rewardAt (k - 1)) =
      expectation M term b s (fun _ e => e.isRatio π b k * e.rewardAt (k - 1)) := by sorry

end SuttonBartoRL.ImportanceSampling
