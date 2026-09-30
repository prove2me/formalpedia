-- Prove2me | Theorems.Thm_SupplyChainTheory_two_matching_cut_form
-- name    : SupplyChainTheory.two_matching_cut_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:54:35.052174+00:00
-- url     : https://prove2.me/theorems/60831e78-de43-46f6-8867-8417805b47fa
-- title:
--   Proposition 10.3: $\sum_{i \in H, j \notin H} x_{ij} + \sum_k \sum_{i \in T_k, j \notin T_k} x_{ij} \ge 3s + 1$ for every tour
-- statement:
--   **Proposition 10.3.** For any handle $H$ and teeth $T_1, \dots, T_s$ satisfying the conditions
--   of Theorem 10.2, every tour through $N$ satisfies
--
--   $$ \sum_{i \in H,\ j \notin H} x_{ij} + \sum_{k=1}^s \sum_{i \in T_k,\ j \notin T_k} x_{ij} \;\ge\; 3s + 1, $$
--
--   the number of tour edges leaving the handle plus the numbers leaving each tooth is at least
--   $3s + 1$. The book's proof: a tooth whose two nodes are joined by a tour edge has two edges
--   leaving it, any other tooth four; each such joined tooth contributes an edge leaving $H$; and
--   the number of edges leaving $H$ is even while $s$ is odd, which forces one extra edge when
--   every tooth is joined.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 414-415, Sect. 10.3.3, Proposition 10.3, Eq. (10.16)-(10.19), and its proof

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem two_matching_cut_form {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T)
    (hteeth : ∀ k, (T k).card = 2) :
    3 * s + 1 ≤ edgesLeaving τ H + ∑ k, edgesLeaving τ (T k) := by sorry

end SupplyChainTheory
