-- Prove2me | Theorems.Thm_RandomGreedyMIS_total_calls_le
-- name    : RandomGreedyMIS.total_calls_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:30:06.410952+00:00
-- url     : https://prove2.me/theorems/ff627b64-82e4-5cff-9ddc-237a8560658d
-- title:
--   Recursive random greedy MIS: $\mathbb E[\text{calls}]\le m/n$
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and $m$ edges. For a ranking $\pi$ of the vertices, let $\mathrm{calls}(v,\pi)$ be the number of recursive calls made by the recursive randomized greedy maximal independent set oracle started at $v$ (which examines lower-ranked neighbours in increasing rank and stops after the first one in the greedy independent set; the top-level call is not counted). Then
--   $$\sum_{\pi}\ \sum_{v}\mathrm{calls}(v,\pi)\ \le\ m\cdot n!,$$
--   the sum running over all $n!$ permutations. Equivalently, for a uniformly random ranking and a uniformly random start vertex, the expected number of recursive calls is at most $m/n$, the average degree divided by two.
--
--   This average-case bound is what makes local simulation of the random greedy maximal independent set (and, on the line graph, of the random greedy maximal matching) cheap, and underlies sublinear estimators of the maximum matching size such as the one used to estimate the conflict-cover cost $\tau$ in the sublinear metric TSP algorithm.
--
--   **Formalization Note** The bound is stated as a sum over all permutations (counting measure) instead of an expectation. It is tight for the path on four vertices.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, A Simple Average-case Analysis of Recursive Randomized Greedy MIS, arXiv:2604.01462 (2026), Theorem 1.1 and Corollary 1.2; originally Yoshida, Yamamoto, Ito, STOC 2009.

import Mathlib
import Definitions.Def_RandomGreedyMIS_basic

namespace RandomGreedyMIS

/-- **Average query complexity of the recursive randomized greedy MIS oracle.** Dalirrooyfard, Makarychev, Mitrović,
*A Simple Average-case Analysis of Recursive Randomized Greedy MIS*, arXiv:2604.01462 (2026), Corollary 1.2 (from
Theorem 1.1): for a uniformly random permutation π and a uniformly random vertex u, the expected number of recursive
calls made by RGMIS(u, π) is at most m/n (Yoshida–Yamamoto–Ito, STOC 2009). Summed over all vertices and all
permutations: `Σ_π Σ_v calls(v, π) ≤ m · n!`. -/
theorem total_calls_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ π : Equiv.Perm (Fin n), ∑ v, (calls G π v : ℝ)) ≤ (G.edgeFinset.card : ℝ) * (Nat.factorial n) := by sorry

end RandomGreedyMIS
