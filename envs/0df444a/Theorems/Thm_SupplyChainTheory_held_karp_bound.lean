-- Prove2me | Theorems.Thm_SupplyChainTheory_held_karp_bound
-- name    : SupplyChainTheory.held_karp_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:00:23.178989+00:00
-- url     : https://prove2.me/theorems/bdb8b16a-1243-49c5-b11b-932f0dc2da95
-- title:
--   Theorem 10.17 (Held-Karp bound): $z^* \ge z(\hat T^*) + \sum_i \lambda_i (d_i(\hat T^*) - 2)$ for every $\lambda$
-- statement:
--   **Theorem 10.17.** For any $\lambda \in \mathbb{R}^n$,
--
--   $$ z^* \;\ge\; z(\hat T^*) + \sum_{i \in N} \lambda_i\big(d_i(\hat T^*) - 2\big), $$
--
--   where $\hat T^*$ is an optimal 1-tree under the revised distances $c'_{ij} = c_{ij} + \lambda_i + \lambda_j$
--   of (10.31) and $d_i(\hat T^*)$ its node degrees. The right-hand side is the Held-Karp lower bound
--   $z_{HK}(\lambda)$; it follows from Lemma 10.15 applied to $c'$ and both parts of Lemma 10.16.
--   Maximizing it over $\lambda$ by subgradient steps (10.34) gives the strongest bounds in practice
--   for the TSP, and the bound is the Lagrangian relaxation of the degree constraints.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 446, Sect. 10.6.1, Theorem 10.17, Eq. (10.33), and its proof; after Held and Karp (1970, 1971)

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem held_karp_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (lam : Fin n → ℝ) (r : Fin n) (G : SimpleGraph (Fin n)) (hG : Is1Tree r G)
    (hopt : ∀ G' : SimpleGraph (Fin n), Is1Tree r G' →
      graphWeight (revisedCost c lam) G ≤ graphWeight (revisedCost c lam) G') :
    graphWeight c G + ∑ i, lam i * ((G.degree i : ℝ) - 2) ≤ optTourLength c := by sorry

end SupplyChainTheory
