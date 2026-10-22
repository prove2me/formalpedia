-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_wstar_holds
-- name    : PartialLostSales.ACOI.wstar_holds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:52.86198+00:00
-- url     : https://prove2.me/theorems/02f3d5be-3eee-4fd1-bdf1-c9c5f884a4ac
-- title:
--   §3.2, p. 12 — Assumption (W*) holds for the lost-sales COMDP: c̄ is K-inf-compact and q is weakly continuous
-- statement:
--   Consider the COMDP of the lost-sales inventory model observed only at zero, under the standing assumptions. Its state space is the set $\mathbb P_2(\mathbb R_+)$ of beliefs with finite second moment, with the topology of weak convergence, and its action set is $\mathbb A=[0,K]$. Then Assumption (W*) holds:
--
--   1. the cost $\bar c(z,a)=\int c(x,a)\,z(dx)$ is $\mathbb K$-inf-compact on $\mathbb P_2(\mathbb R_+)\times\mathbb A$. That is, for every nonempty compact set $\mathcal K$ of beliefs and every $\lambda\in\mathbb R$, the set $\{(z,a)\in\mathcal K\times\mathbb A:\bar c(z,a)\le\lambda\}$ is compact;
--   2. the transition kernel $q(\cdot\mid z,a)$ is weakly continuous in $(z,a)$. That is, for every bounded continuous $f$ on beliefs,
--   $$(z,a)\mapsto\int f(z')\,q(dz'\mid z,a)$$
--   is continuous.
--
--   The paper states this on p. 12 and attributes it to Feinberg, Kasyanov and Zgurovsky (2016), who prove (W*) for a more general partially observable inventory model. It is the continuity hypothesis of Lemma 1 and Lemma 2.
--
--   **Formalization Note.** The inventory space $\mathbb R_+$ carries its Euclidean topology, and beliefs the weak-convergence topology inherited from all probability measures on $\mathbb R_+$. Weak continuity is tested against bounded continuous real functions on beliefs.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 12, §3.2, first paragraph

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- §3.2, p. 12: Assumption (W*) holds for the COMDP: `c̄` is `𝕂`-inf-compact on
`ℙ(𝕏) × 𝔸` and `q` is weakly continuous, beliefs carrying the weak topology. -/
theorem wstar_holds (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    AssumptionWStar M := by sorry

end PartialLostSales.ACOI
