-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_steady_state_is_stationary
-- name    : SuttonBartoRL.AverageReward.steady_state_is_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:00:21.994989+00:00
-- url     : https://prove2.me/theorems/aaba67e5-5139-4ca0-8c97-f0a3e5788047
-- title:
--   (10.8): the steady-state distribution $\mu_\pi$ is stationary
-- statement:
--   Let $\pi$ be a policy in a finite MDP with at least one state, and suppose the steady-state distribution $\mu(s) = \lim_{t\to\infty}\Pr\{S_t = s\mid S_0 = s_0,\ A_{0:t-1}\sim\pi\}$ exists for every $s$ and does not depend on $s_0$. Then $\mu$ is a probability distribution on the states and, if one selects actions according to $\pi$, one remains in the same distribution:
--   $$
--   \sum_s \mu(s)\sum_a \pi(a\mid s)\, p(s'\mid s, a) = \mu(s') \qquad\text{for all } s' .
--   $$
--
--   Together with the previous result it says that the limiting distribution of an ergodic MDP is a stationary distribution, which is the only property of $\mu_\pi$ that the argument of §10.4 uses.
--
--   **Formalization Note** "Probability distribution" means $\mu(s) \ge 0$ and $\sum_s\mu(s) = 1$; the nonempty state space is needed for the latter.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (10.8), p. 249

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

open Filter Topology

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), (10.8), p. 249: the steady-state distribution
`μ(s) = lim_{t→∞} Pr{S_t = s | A_{0:t-1} ∼ π}`, when it exists and is independent of `S_0`, is a
probability distribution under which, selecting actions according to `π`, one remains in the same
distribution: `Σ_s μ(s) Σ_a π(a | s) p(s' | s, a) = μ(s')`. -/
theorem steady_state_is_stationary {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (hμ : ∀ s₀ s, Tendsto (fun t : ℕ => M.stateDist π s₀ t s) atTop (𝓝 (μ s))) :
    IsStationaryDist M π μ := by sorry

end SuttonBartoRL.AverageReward
