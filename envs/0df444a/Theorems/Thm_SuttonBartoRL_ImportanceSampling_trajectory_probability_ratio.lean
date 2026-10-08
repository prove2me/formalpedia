-- Prove2me | Theorems.Thm_SuttonBartoRL_ImportanceSampling_trajectory_probability_ratio
-- name    : SuttonBartoRL.ImportanceSampling.trajectory_probability_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:50:38.419989+00:00
-- url     : https://prove2.me/theorems/8609a942-945c-4590-bbf8-cdcb2027005a
-- title:
--   Trajectory probability and the importance-sampling ratio (5.3)
-- statement:
--   Consider a finite MDP with terminal states, a start state $s$, target and behaviour policies $\pi$ and $b$, and a fixed state–action sequence $S_0, A_0, S_1, \dots, A_{n-1}, S_n$.
--
--   1. For every policy $\mu$, summing the probability of the episode over its rewards $R_1, \dots, R_n$ gives the probability of the state–action trajectory:
--   $$
--   \Pr\{A_0, S_1, \dots, S_n \mid S_0 = s, A_{0:n-1} \sim \mu\} = \prod_{k=0}^{n-1} \mu(A_k \mid S_k)\, p(S_{k+1} \mid S_k, A_k)
--   $$
--   (and $0$ if the sequence does not start at $s$, or reaches a terminal state before $n$ or not at $n$).
--
--   2. If the trajectory has positive probability under $b$, then the ratio of its probabilities under $\pi$ and $b$ is the importance-sampling ratio, which does not involve the dynamics:
--   $$
--   \rho_{0:n-1} = \frac{\prod_{k=0}^{n-1} \pi(A_k \mid S_k)\, p(S_{k+1} \mid S_k, A_k)}{\prod_{k=0}^{n-1} b(A_k \mid S_k)\, p(S_{k+1} \mid S_k, A_k)} = \prod_{k=0}^{n-1} \frac{\pi(A_k \mid S_k)}{b(A_k \mid S_k)} .
--   $$
--
--   This is why the importance-sampling ratio can be computed without knowing the MDP.
--
--   **Formalization Note** Times are shifted so that $t = 0$ and $T = n$. The ratio $\rho_{0:n-1}$ is evaluated on the episode with the given states and actions and any rewards; it depends on states and actions only.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, trajectory probability display and Eq. (5.3), p. 104

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Episodes

namespace SuttonBartoRL.ImportanceSampling

/-- Sutton & Barto (2018), §5.5, p. 104, display before (5.3) and Eq. (5.3). (i) Summing the
reward-inclusive episode probability over the rewards gives the probability of the state–action
trajectory, `Π_{k} μ(A_k|S_k) p(S_{k+1}|S_k, A_k)`. (ii) Whenever the trajectory has positive
probability under the behaviour policy `b`, the ratio of its probabilities under `π` and `b` is the
importance-sampling ratio `ρ_{0:T-1} = Π_{k=0}^{T-1} π(A_k|S_k)/b(A_k|S_k)`, which does not involve
the MDP's dynamics. -/
theorem trajectory_probability_ratio {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (term : Finset S) (π b : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (n : ℕ)
    (st : Fin (n + 1) → S) (ac : Fin n → A) :
    (∀ μ : SuttonBartoRL.FiniteMDP.Policy S A,
      ∑ rw : Fin n → M.R, episodeProb M term μ s ((st, ac, rw) : Episode M n) =
        trajectoryProb M term μ s st ac) ∧
    (trajectoryProb M term b s st ac ≠ 0 → ∀ rw : Fin n → M.R,
      trajectoryProb M term π s st ac / trajectoryProb M term b s st ac =
        Episode.isRatio π b ((st, ac, rw) : Episode M n) n) := by sorry

end SuttonBartoRL.ImportanceSampling
