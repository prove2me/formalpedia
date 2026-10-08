-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_z_standard_average_cost
-- name    : SennottDP.MarkovCost.z_standard_average_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T14:11:19.008558+00:00
-- url     : https://prove2.me/theorems/56be0296-385d-4569-bf00-c1ff131baa89
-- title:
--   Proposition C.2.6 — a $z$ standard chain has one positive recurrent class, finite $J_R$, and $J^{(n)}_i \to J_R$ for all $i$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with finite nonnegative costs $C(i)$, and assume that $\Gamma$ is $z$ standard: $m_{iz} < \infty$ and $c_{iz} < \infty$ for all $i \in S$. Then:
--
--   1. $S$ decomposes into a positive recurrent class $R$ containing $z$ and a set $U = S - R$ of transient states;
--   2. the average cost $J_R = \sum_{j \in R} \pi_j C(j)$ on $R$ is finite;
--   3. for every $i \in S$,
--   $$ \lim_{n \to \infty} J^{(n)}_i = J_R. $$
--
--   So under the $z$ standard hypothesis the long-run expected average cost is the same finite constant from every initial state, which is what makes the chain usable in average cost optimization.
--
--   **Formalization Note** The limit is taken in $[0,\infty]$ and $J^{(n)}_i = \frac1n\sum_{t<n}\sum_j P^{(t)}_{ij}C(j)$. Part 1 is stated as: $R$ is a positive recurrent class containing $z$ and every state outside $R$ is transient.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 301, Proposition C.2.6 (with Definition C.2.5)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.6, p. 301. Assume that the Markov chain with costs is `z`
standard. Then
(i) `S` decomposes into a positive recurrent class `R` containing `z` and a set `U = S − R` of
transient states;
(ii) the average cost `J_R` on `R` is finite;
(iii) `lim_{n→∞} J^{(n)}_i` exists and equals `J_R` for all `i ∈ S`. -/
theorem z_standard_average_cost {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (z : S)
    (hz : IsZStandard M C z) :
    ∃ R : Set S, IsPosRecClass M R ∧ z ∈ R ∧ (∀ i ∉ R, Transient M i) ∧
      classAvgCost M C R < ⊤ ∧
      ∀ i, Tendsto (fun n : ℕ => avgCostN M C n i) atTop (𝓝 (classAvgCost M C R)) := by sorry

end SennottDP.MarkovCost
