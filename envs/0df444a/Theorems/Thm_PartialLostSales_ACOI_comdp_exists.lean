-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_comdp_exists
-- name    : PartialLostSales.ACOI.comdp_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:34.491035+00:00
-- url     : https://prove2.me/theorems/ba4f7907-ae35-417e-811a-7952837e4189
-- title:
--   §3.1, p. 10 — the belief transition kernel q(·|z,a) of the lost-sales COMDP is a measurable stochastic kernel
-- statement:
--   Consider the lost-sales inventory model observed only at zero, under its standing assumptions. Let $\mathbb P_2(\mathbb R_+)$ be the beliefs with finite second moment, $\mathbb A=[0,K]$, $\bar c$ the belief cost (7), and $q(\cdot\mid z,a)$ the belief transition (6):
--   $$q(\cdot\mid z,a)=R(0\mid z,a)\,\delta_{\delta_0}+R(1\mid z,a)\,\delta_{H(z,a,1)}.$$
--   Then there is a Markov decision process on $\mathbb P_2(\mathbb R_+)\times\mathbb A$ whose cost is $\bar c$ and whose transition probability is $q$. In other words, $(z,a)\mapsto q(\cdot\mid z,a)$ is a measurable stochastic kernel from $\mathbb P_2(\mathbb R_+)\times\mathbb A$ to $\mathbb P_2(\mathbb R_+)$.
--
--   The paper asserts this on p. 10: the posterior map $H$ is measurable, and $z_{t+1}$ has a distribution uniquely determined by the stochastic kernel $q$. Every other statement of the mission is about this COMDP, so this result guarantees that none of them is vacuous.
--
--   **Formalization Note.** The statement is the existence of an `MDP` satisfying `IsCOMDP`. That predicate pins the lower bound $0$, the cost $\bar c$ and the kernel $q$ pointwise, so such an MDP is unique. What has to be shown is that $q$ is measurable in $(z,a)$ and is a probability measure.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 10, §3.1 (5), (6)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- §3.1, p. 10: the COMDP exists — the belief transition `q(· | z, a)` of (6) is a measurable
Markov kernel on the beliefs with finite second moment. -/
theorem comdp_exists (P : Params) (hP : Standing P) :
    ∃ M : MDP (Bel P) (Act P), IsCOMDP P M := by sorry

end PartialLostSales.ACOI
