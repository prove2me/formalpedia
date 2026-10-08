-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_optimal_iff_dp
-- name    : ShapiroSDDP.Convergence.optimal_iff_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:47.059764+00:00
-- url     : https://prove2.me/theorems/5b4fc128-f40a-4b9a-b838-4be3ab81829f
-- title:
--   Proof of Proposition 3.1, pp. 10–11 — a policy is optimal for the SAA problem iff it satisfies the DP conditions (3.18)
-- statement:
--   Assume the SAA cost-to-go functions are finite valued on reachable decisions. Let $\bar x_t=\bar x_t(\tilde\xi_{[t]})$, $t=1,\dots,T$, be an implementable policy of the SAA problem. Then the policy is optimal, that is feasible with minimal expected cost
--   $$\frac1N\sum_{\text{scenarios}}\sum_{t=1}^T\tilde c_t^\top\bar x_t$$
--   among all feasible implementable policies, if and only if the dynamic programming optimality conditions
--   $$\bar x_t(\tilde\xi_{[t]})\in\arg\min_{x_t}\big\{\tilde c_t^\top x_t+\widetilde{\mathcal Q}_{t+1}(x_t):\ \tilde B_t\bar x_{t-1}(\tilde\xi_{[t-1]})+\tilde A_tx_t=\tilde b_t,\ x_t\ge0\big\}\tag{3.18}$$
--   hold for $t=1,\dots,T$ and every scenario of the SAA problem, where at stage 1 the constraint is $A_1x_1=b_1$ (the paper's convention $\tilde B_0=0$) and $\widetilde{\mathcal Q}_{T+1}\equiv0$.
--
--   The paper recalls this as a classical result (p. 6 and p. 10); in the proof of Proposition 3.1 it reduces optimality of the forward policy to (3.18).
--
--   **Formalization Note** Optimality is defined by expected cost, so this equivalence is not definitional. Since every scenario has positive probability $1/N$, (3.18) must hold on every scenario, not only almost surely.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, pp. 10–11, proof of Proposition 3.1, (3.18); also p. 6, §3

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model

namespace ShapiroSDDP.Convergence

/-- Proof of Proposition 3.1, pp. 10–11 (and §3, p. 6): with finite-valued cost-to-go functions, an
implementable policy of the SAA problem is optimal (minimal expected cost (3.15) among feasible
implementable policies) if and only if it satisfies the dynamic programming optimality conditions
(3.18) at every stage and on every scenario. -/
theorem optimal_iff_dp (I : Instance) (hfin : FiniteValued I) (pol : Policy I)
    (hpol : IsImplementable I pol) :
    IsOptimalPolicy I pol ↔ DPOptimal I pol := by sorry

end ShapiroSDDP.Convergence
