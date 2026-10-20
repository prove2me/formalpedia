-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_reformulation_9
-- name    : TimeLockedSales.Reform.reformulation_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:40.804428+00:00
-- url     : https://prove2.me/theorems/bf3ec657-81f5-425a-ba7e-17f8ff63889e
-- title:
--   §4.2, p. 17 — recommendation-policy formulation (9) has the platform's optimal value
-- statement:
--   In the paper's focus region, let $R(\sigma)$ be the expected revenue under any finite-message information policy with customers following the Bayesian purchase rule (2). Let $(r,z)$ satisfy the recommendation distributions (R), state evolution (N), and the four incentive inequalities on page 17. Then formulation (9) attains an objective value $J$ that is the least upper bound of all original-policy revenues:
--   $$J=\max_{(r,z)\text{ feasible for (9)}}p\sum_{t=1}^T\sum_n z_t(n)\bigl(r_t^1(n)+u_nr_t^0(n)\bigr)=\sup_{\sigma}R(\sigma).$$
--   This is the link from the original dynamic information-design problem to the finite-state optimization problem.
--
--   **Formalization Note.** The supremum ranges over all finite-message policies, not only recommendation policies. A maximum is asserted for (9), while the original-policy value is expressed as a least upper bound because the printed weak IC constraints can create response ties. The integer range is $n=-(T-1),\ldots,T-1$, and $t=1,\ldots,T$. The price and signal assumptions and focus region are explicit.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), p. 17, §4.2, reformulation (9)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- The unnumbered reformulation (9), p. 17, of the original problem (3). -/
theorem reformulation_9 (P : Params) (hS : P.Standing) (hR : P.Region) :
    ∃ J : ℝ,
      IsGreatest {K | ∃ r z, Feasible9 P r z ∧ K = obj9 P r z} J ∧
      IsLUB (AchievableRevenue P) J := by sorry

end TimeLockedSales.Reform
