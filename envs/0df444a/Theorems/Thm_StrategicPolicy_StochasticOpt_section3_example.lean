-- Prove2me | Theorems.Thm_StrategicPolicy_StochasticOpt_section3_example
-- name    : StrategicPolicy.StochasticOpt.section3_example
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T13:00:32.537033+00:00
-- url     : https://prove2.me/theorems/6e57f113-9046-4a6b-96d4-11641b6bd3d1
-- title:
--   §3, p. 5, example after (8) — the optimal policies are exactly π = (1, 0.7, s) with s ≤ 0.4, all stochastic, with utility 0.66
-- statement:
--   Consider the three-value instance of §3: $x\in\{1,2,3\}$, $\gamma=0.1$, $P(x)=(0.1,0.4,0.5)$, $P(y=1\mid x)=(1.0,0.7,0.4)$ and the cost matrix of p. 5, with individuals best responding by (5) and tie-break (ii). Let $u(\pi,\gamma)$ be the strategic utility (7), and call a policy optimal if it maximizes $u$ over all policies $\pi$ with values in $[0,1]$.
--
--   1. A policy $\pi$ is optimal if and only if
--   $$
--   \pi(x=1)=1,\qquad \pi(x=2)=0.7,\qquad \pi(x=3)\le0.4 .
--   $$
--   2. No optimal policy is deterministic: every optimal policy takes some value outside $\{0,1\}$.
--   3. The policy $\pi^*=(1,0.7,0)$ has utility $u(\pi^*,\gamma)=0.66$.
--
--   In particular the policy printed in the paper, $(1,0.7,0)$, is optimal, and in contrast with the non-strategic setting, where the deterministic threshold rule is optimal, every strategic optimum is stochastic, even though the cost is outcome monotonic.
--
--   **Formalization Note** The paper prints a single optimal policy; the optimum is not unique, and item 1 states the full set (at $\pi(x=3)=0.4$ the individuals at $x=3$ tie between staying and moving to $x=2$, and tie-break (ii) sends them to $x=2$). In Lean the feature values $1,2,3$ are the indices $0,1,2$. Optimality is `IsMaxOn` over the whole set $[0,1]^3$, not over a finite grid.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 5, §3, example after (8)

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example

namespace StrategicPolicy.StochasticOpt

theorem section3_example :
    (∀ π ∈ Policies 3,
      IsMaxOn (u p0 q0 γ0 c0) (Policies 3) π ↔ (π 0 = 1 ∧ π 1 = 7 / 10 ∧ π 2 ≤ 2 / 5)) ∧
    (∀ π ∈ Policies 3, IsMaxOn (u p0 q0 γ0 c0) (Policies 3) π → ¬ IsDeterministic π) ∧
    u p0 q0 γ0 c0 ![1, 7 / 10, 0] = 33 / 50 := by sorry

end StrategicPolicy.StochasticOpt
