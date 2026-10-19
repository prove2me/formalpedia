-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_greedy_fill_structure
-- name    : StochKnapSL.CapacityGap.greedy_fill_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:17.681003+00:00
-- url     : https://prove2.me/theorems/161142e7-2804-4c2d-bed1-d10939670d84
-- title:
--   Proof of Theorem 3, p. 17 — the greedy fill is fractional for at most one customer, and positive iff the demand ahead is below Q
-- statement:
--   Fix a priority order $\sigma$ on customers $\{1,\dots,N\}$, a capacity $Q \ge 0$ and non-negative demands $x_1, \dots, x_N$. The greedy fractional fill gives customer $i$ the amount
--   $$ x^*_i = \min\Big\{x_i,\ \max\Big(0,\ Q - \sum_{j \text{ ahead of } i \text{ in } \sigma} x_j\Big)\Big\}. $$
--   Then:
--   1. $x^*_i \notin \{0, x_i\}$ for at most one customer $i$;
--   2. for every customer with $x_i > 0$, $x^*_i > 0$ holds if and only if $\sum_{j \text{ ahead of } i} x_j < Q$.
--
--   The second condition does not involve $x_i$. The proof of Theorem 3 uses this to make the event "customer $i$ receives something" independent of $\tilde d_i$.
--
--   **Formalization Note.** The statement is pointwise in the demand vector. The paper's demands are positive, and the hypothesis $x_i > 0$ in part 2 is that positivity: with $x_i = 0$ the fill is $0$ whatever the demand ahead.
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 17, proof of Theorem 3 ('Note that the greedy solution …')

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- Proof of Theorem 3, p. 17: the greedy fractional-knapsack solution is fractional
(neither `0` nor the full demand) for at most one customer, and a customer with positive demand
receives a positive amount iff the demand ahead of her is below the capacity. -/
theorem greedy_fill_structure {N : ℕ} (σ : Equiv.Perm (Fin N)) (Q : ℝ) (x : Fin N → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hQ : 0 ≤ Q) :
    {i : Fin N | fill σ Q x i ≠ 0 ∧ fill σ Q x i ≠ x i}.Subsingleton ∧
      ∀ i, 0 < x i → (0 < fill σ Q x i ↔ ∑ j ∈ ahead σ i, x j < Q) := by sorry

end StochKnapSL.CapacityGap
