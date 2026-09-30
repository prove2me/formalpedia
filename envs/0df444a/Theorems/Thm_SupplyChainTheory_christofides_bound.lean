-- Prove2me | Theorems.Thm_SupplyChainTheory_christofides_bound
-- name    : SupplyChainTheory.christofides_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:01:09.310204+00:00
-- url     : https://prove2.me/theorems/f9b2f82f-3573-4999-9be2-553b9df303d7
-- title:
--   Theorem 10.13 (Christofides): the tour returned by Christofides' heuristic satisfies $z_{CH}/z^* \le 3/2$
-- statement:
--   **Theorem 10.13.** For every instance of the TSP that satisfies the triangle inequality,
--
--   $$ \frac{z_{CH}}{z^*} \;\le\; \frac{3}{2}, $$
--
--   where $z^*$ is the length of the optimal tour and $z_{CH}$ the length of the tour returned by
--   Christofides' heuristic (Algorithm 10.6): find a minimum spanning tree $T^*$, find a
--   minimum-weight perfect matching $M$ on the odd-degree nodes of $T^*$, take an Eulerian tour of
--   the graph formed by the edges of $T^*$ and of $M$ (an edge may appear in both), and shortcut it
--   by visiting the nodes in order of first appearance.
--
--   The book's proof: $z(T^*) \le z^*$ by Lemma 10.9; the optimal tour restricted to the odd nodes by
--   shortcutting has length at most $z^*$ and splits into two perfect matchings on those nodes, so
--   $z(M) \le \frac{1}{2} z^*$; the Eulerian tour has length $z(T^*) + z(M) \le \frac{3}{2}z^*$, and
--   shortcutting does not lengthen it. This is the best worst-case bound known for the metric TSP;
--   Problem 10.13 shows it is tight, and Lemma 10.18 records that it holds even against the LP
--   relaxation.
--
--   **Formalization Note** The graph $T^* + M$ is a multigraph when a matching edge repeats a tree
--   edge, so it is represented by its Eulerian walk: a closed walk in the complete graph whose edge
--   multiset is the sum of the tree's and the matching's. Every MST, minimum matching, Eulerian tour
--   and start node is covered.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 433-435, Sect. 10.4.7, Theorem 10.13, Eq. (10.28)-(10.29), and its proof; Algorithm 10.6; after Christofides (1976)

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem christofides_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) (M : Finset (Sym2 (Fin n)))
    (hM : IsMinMatchingOn c (oddNodes T) M) (v : Fin n) (W : (⊤ : SimpleGraph (Fin n)).Walk v v)
    (hW : (W.edges : Multiset (Sym2 (Fin n))) = T.edgeFinset.val + M.val)
    (τ : Equiv.Perm (Fin n)) (hτ : IsShortcut W.support τ) :
    tourLength c τ ≤ (3 / 2 : ℝ) * optTourLength c := by sorry

end SupplyChainTheory
