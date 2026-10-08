-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_class_average_cost
-- name    : SennottDP.MarkovCost.class_average_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:58:14.108781+00:00
-- url     : https://prove2.me/theorems/c361bd97-849e-43dd-bb42-d2042b4a02f9
-- title:
--   Proposition C.2.1 — on a positive recurrent class, $J^{(n)}_i \to J_R = c_{ii}/m_{ii}$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with finite nonnegative costs $C(i)$, let $R$ be a positive recurrent class, and let
--   $$ J_R = \sum_{j \in R} \pi_j C(j) \in [0,\infty]. $$
--
--   1. For $i \in R$, $\lim_{n\to\infty} J^{(n)}_i$ exists and equals $J_R$ (finite or infinite).
--   2. For $i \in R$, $J_R = c_{ii}/m_{ii}$, the expected cost of a return to $i$ divided by the expected return time.
--   3. For every $n \ge 0$,
--   $$ J_R = \sum_{j \in R} \pi_j\, E[C(X_n) \mid X_0 = j]. $$
--
--   The result identifies the long-run average cost from any state of a positive recurrent class as a single constant.
--
--   **Formalization Note** $E[C(X_n)\mid X_0=j] = \sum_k P^{(n)}_{jk} C(k)$; limits are taken in $[0,\infty]$, so part 1 covers $J_R = \infty$. $m_{ii}$ is finite and at least $1$ on a positive recurrent class.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 298, Proposition C.2.1, Eq. (C.11)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.1, p. 298. Let `R` be a positive recurrent class and
`J_R = ∑_{j ∈ R} π_j C(j)` (finite or infinite).
(i) For `i ∈ R`, `lim_{n→∞} J^{(n)}_i` exists and equals `J_R`.
(ii) For `i ∈ R`, `J_R = c_{ii}/m_{ii}`.
(iii) `J_R = ∑_{j ∈ R} π_j E[C(X_n) | X_0 = j]` for `n ≥ 0`. -/
theorem class_average_cost {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (R : Set S)
    (hR : IsPosRecClass M R) :
    (∀ i ∈ R, Tendsto (fun n : ℕ => avgCostN M C n i) atTop (𝓝 (classAvgCost M C R))) ∧
    (∀ i ∈ R, classAvgCost M C R = passageCost M C {i} i / meanPassage M {i} i) ∧
    (∀ n : ℕ, classAvgCost M C R =
      ∑' j : R, steadyState M j * ∑' k, nStep M n j k * (C k : ℝ≥0∞)) := by sorry

end SennottDP.MarkovCost
