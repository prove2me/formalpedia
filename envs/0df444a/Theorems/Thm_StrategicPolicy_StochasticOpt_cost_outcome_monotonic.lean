-- Prove2me | Theorems.Thm_StrategicPolicy_StochasticOpt_cost_outcome_monotonic
-- name    : StrategicPolicy.StochasticOpt.cost_outcome_monotonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T13:00:28.032253+00:00
-- url     : https://prove2.me/theorems/29a57d79-dae3-407e-9176-d93c0d2e9c28
-- title:
--   §3, p. 5, example after (8) — the instance's cost is outcome monotonic and satisfies standing assumption (i)
-- statement:
--   In the three-value instance of §3 ($x\in\{1,2,3\}$ with $P(y=1\mid x)=(1.0,0.7,0.4)$ and the cost matrix of p. 5), the cost $c$ is **outcome monotonic**: $c(x,x)=0$; for pairwise distinct $i,j,k$,
--   $$
--   P(y=1\mid x_i)<P(y=1\mid x_j)<P(y=1\mid x_k)\iff \bigl[c(x_i,x_j)<c(x_i,x_k)\bigr]\wedge\bigl[c(x_j,x_k)<c(x_i,x_k)\bigr];
--   $$
--   and for $i\ne j$, $P(y=1\mid x_i)>P(y=1\mid x_j)\iff c(x_i,x_j)=0$. Moreover it satisfies standing assumption (i): $c(x_i,x_j)>0$ whenever $i\ne j$ and $P(y\mid x_j)\ge P(y\mid x_i)$.
--
--   This is the hypothesis "even under outcome monotonic costs" under which the example is posed, and it confirms that the instance belongs to the paper's model.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 5, §3, sentence before the example; outcome monotonic cost p. 6; standing assumption (i) p. 4

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example

namespace StrategicPolicy.StochasticOpt

theorem cost_outcome_monotonic : OMCost q0 c0 ∧ StandingI q0 c0 := by sorry

end StrategicPolicy.StochasticOpt
