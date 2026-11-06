-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_dp_implies_optimal
-- name    : ShapiroSDDP.Convergence.dp_implies_optimal
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T16:49:50.24257+00:00
-- url     : https://prove2.me/theorems/f87bdc8d-57bb-4de8-9d3d-18b738f92d04
-- title:
--   Proof of Proposition 3.1, p. 10 — a policy satisfying the DP optimality conditions (3.18) is optimal for the SAA problem
-- statement:
--   Consider the SAA of a multistage linear stochastic program with $T\ge2$ stages, whose cost-to-go functions $\widetilde{\mathcal Q}_{t+1}$ are finite valued on reachable decisions. Let $\bar x_t=\bar x_t(\tilde\xi_{[t]})$, $t=1,\dots,T$, be an implementable policy that satisfies the dynamic programming optimality conditions (3.18) on every scenario:
--   $$\bar x_t(\tilde\xi_{[t]})\in\arg\min_{x_t}\big\{\tilde c_t^\top x_t+\widetilde{\mathcal Q}_{t+1}(x_t):\ \tilde B_t\bar x_{t-1}(\tilde\xi_{[t-1]})+\tilde A_tx_t=\tilde b_t,\ x_t\ge0\big\},\qquad t=1,\dots,T,$$
--   with $\tilde B_1=0$ and $\widetilde{\mathcal Q}_{T+1}\equiv0$. Then $\bar x$ is an optimal policy of the SAA problem: it is feasible, and its expected cost $\frac1N\sum_{s}\sum_{t=1}^T\tilde c_t(s)^\top\bar x_t(s)$ (3.15) is at most the expected cost of every feasible implementable policy.
--
--   This is the "if" direction of the equivalence "a policy is optimal for the SAA problem iff (3.18) holds", which the proof of Proposition 3.1 uses to conclude that the forward-step policy is optimal once the cutting-plane approximations are exact along all forward paths.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 10, proof of Proposition 3.1 (sufficiency of the dynamic programming optimality conditions (3.18))

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model

namespace ShapiroSDDP.Convergence

/-- Proof of Proposition 3.1, p. 10 (sufficiency half of the dynamic programming optimality
conditions (3.18)): with finite-valued cost-to-go functions, an implementable policy that satisfies
(3.18) at every stage and on every scenario of the SAA problem is optimal, i.e. it is feasible and
its expected cost (3.15) is at most that of every feasible implementable policy. -/
theorem dp_implies_optimal (I : Instance) (hfin : FiniteValued I) (pol : Policy I)
    (hpol : IsImplementable I pol) (hdp : DPOptimal I pol) : IsOptimalPolicy I pol := by sorry

end ShapiroSDDP.Convergence
