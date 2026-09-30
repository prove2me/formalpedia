-- Prove2me | Theorems.Thm_SupplyChainTheory_two_matching_inequality
-- name    : SupplyChainTheory.two_matching_inequality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:53:23.586722+00:00
-- url     : https://prove2.me/theorems/bda7b46b-33da-4c30-be85-d8eb3e4ded0d
-- title:
--   Theorem 10.2: the 2-matching inequality $\sum_{i,j \in H} x_{ij} + \sum_k \sum_{i,j \in T_k} x_{ij} \le |H| + \tfrac{1}{2}(s-1)$ holds for every tour
-- statement:
--   **Theorem 10.2.** For any handle $H \subseteq N$ and teeth $T_1, \dots, T_s \subseteq N$ such that
--   each $T_k$ contains exactly one node in $H$ and one node not in $H$, the teeth are pairwise
--   disjoint, and $s \ge 3$ is odd, the 2-matching (blossom) inequality
--
--   $$ \sum_{i,j \in H} x_{ij} + \sum_{k=1}^s \sum_{i,j \in T_k} x_{ij} \;\le\; |H| + \tfrac{1}{2}(s-1) $$
--
--   is valid for every tour through $N$, where $x_{ij} = 1$ when the tour uses edge $\{i, j\}$. The
--   book's proof counts degrees: if the left side reached $|H| + \frac{1}{2}(s+1)$, the nodes of $H$
--   would have total degree at least $2|H| + 1$, so some node would have degree greater than $2$.
--   Here the count is over the edge set of a tour on $n \ge 3$ nodes, and $\tfrac{1}{2}(s-1)$ is the
--   exact natural number since $s$ is odd.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 413-414, Sect. 10.3.3, Theorem 10.2, Eq. (10.15), and its proof; after Hong (1972)

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem two_matching_inequality {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T)
    (hteeth : ∀ k, (T k).card = 2) :
    edgesWithin τ H + ∑ k, edgesWithin τ (T k) ≤ H.card + (s - 1) / 2 := by sorry

end SupplyChainTheory
