-- Prove2me | Theorems.Thm_SupplyChainTheory_comb_inequality
-- name    : SupplyChainTheory.comb_inequality
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:55:34.287331+00:00
-- url     : https://prove2.me/theorems/5769a80a-1b33-435c-96c8-379b7fa64ab0
-- title:
--   Theorem 10.4: the comb inequality $\sum_{i,j \in H} x_{ij} + \sum_k \sum_{i,j \in T_k} x_{ij} \le |H| + \sum_k (|T_k| - 1) + \tfrac{1}{2}(s-1)$ holds for every tour
-- statement:
--   **Theorem 10.4.** For any handle $H \subseteq N$ and teeth $T_1, \dots, T_s \subseteq N$ such that
--   each $T_k$ contains at least one node in $H$ and one node not in $H$, the teeth are pairwise
--   disjoint, and $s \ge 3$ is odd, the comb inequality
--
--   $$ \sum_{i,j \in H} x_{ij} + \sum_{k=1}^s \sum_{i,j \in T_k} x_{ij} \;\le\; |H| + \sum_{k=1}^s (|T_k| - 1) - \tfrac{1}{2}(s+1) $$
--
--   is valid for every tour through $N$. The book omits the proof (Problem 10.10). Combs
--   generalize the 2-matching inequalities to teeth of any size; Grötschel and Padberg showed
--   that together with the subtour-elimination constraints they define facets of the TSP polytope,
--   which is why they are the cuts of choice in branch-and-cut codes.
--
--   **Formalization Note** The book prints (10.20) with $+\tfrac{1}{2}(s-1)$ in place of
--   $-\tfrac{1}{2}(s+1)$. That is a typo. With teeth of two nodes, $\sum_k(|T_k| - 1) = s$, and the
--   printed right side becomes $|H| + s + \tfrac{1}{2}(s-1)$. The book's own 2-matching inequality
--   (10.15), which it presents as the special case, is $|H| + \tfrac{1}{2}(s-1)$. So is the corrected
--   form, which is the standard comb inequality (Grötschel and Padberg 1979; Chvátal). The printed
--   form is true but weaker by $s$ and never tight. This statement is the corrected one, which
--   implies the printed one. It is written with the $\tfrac{1}{2}(s+1)$ on the left, so no
--   natural-number subtraction truncates, and $(s+1)/2$ is exact for odd $s$. It was checked by
--   enumerating every tour for $n = 6$ to $9$ against random combs: no violation, and tight in
--   thousands of cases.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 415, Sect. 10.3.3, Theorem 10.4, Eq. (10.20): 'Proof. Omitted; see Problem 10.10'; after Grötschel and Padberg (1979)

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem comb_inequality {n s : ℕ} (hn : 3 ≤ n) (τ : Equiv.Perm (Fin n))
    (H : Finset (Fin n)) (T : Fin s → Finset (Fin n)) (hcomb : IsComb H T) :
    edgesWithin τ H + ∑ k, edgesWithin τ (T k) + (s + 1) / 2
      ≤ H.card + ∑ k, ((T k).card - 1) := by sorry

end SupplyChainTheory
