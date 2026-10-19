-- Prove2me | Theorems.Thm_StrategicPolicy_StochasticOpt_induced_transport
-- name    : StrategicPolicy.StochasticOpt.induced_transport
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:00:28.573826+00:00
-- url     : https://prove2.me/theorems/956fcb36-504e-4f39-afec-7606ffedf638
-- title:
--   §3, p. 5, example after (8) — π* = (1, 0.7, 0) moves x = 3 to x = 2 and x = 2 to x = 1
-- statement:
--   In the three-value instance of §3, take the policy $\pi^*=(\pi^*(x=1),\pi^*(x=2),\pi^*(x=3))=(1,\,0.7,\,0)$. Then the best responses (5), with tie-break (ii), are
--   $$
--   \mathrm{br}(3)=2,\qquad \mathrm{br}(2)=1,\qquad \mathrm{br}(1)=1 .
--   $$
--   So the mass $P(x=3)$ is transported to $P(x=2\mid\pi^*)$ and the mass $P(x=2)$ to $P(x=1\mid\pi^*)$.
--
--   An individual at $x=2$ is indifferent between staying ($0.7$) and moving to $x=1$ ($1-0.3=0.7$); tie-break (ii) sends them to the higher outcome $x=1$.
--
--   **Formalization Note** In Lean the feature values $1,2,3$ are the indices $0,1,2$, so the statement reads `br 2 = 1`, `br 1 = 0`, `br 0 = 0`.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 5, §3, example after (8), clause "inducing a transportation of mass"

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example

namespace StrategicPolicy.StochasticOpt

theorem induced_transport :
    br c0 q0 ![1, 7 / 10, 0] 2 = 1 ∧ br c0 q0 ![1, 7 / 10, 0] 1 = 0 ∧
      br c0 q0 ![1, 7 / 10, 0] 0 = 0 := by sorry

end StrategicPolicy.StochasticOpt
