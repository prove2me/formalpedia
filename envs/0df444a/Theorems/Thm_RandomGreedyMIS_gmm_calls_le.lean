-- Prove2me | Theorems.Thm_RandomGreedyMIS_gmm_calls_le
-- name    : RandomGreedyMIS.gmm_calls_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:35:08.472213+00:00
-- url     : https://prove2.me/theorems/3601d5ee-44b0-503e-8ff7-c5b0ab010f0d
-- title:
--   Local greedy matching oracle: total calls $\le\sum_v\binom{\deg v}2\cdot m!$
-- statement:
--   Let $H$ be a finite simple graph on $\{0,\dots,n-1\}$ with $m$ edges and degrees $\deg v$. For a ranking $\sigma$ of the edges and an edge $i$, let $\mathrm{calls}(i,\sigma)$ be the number of recursive calls of the greedy MIS oracle on the line graph $L(H)$ started at $i$. Then
--   $$\sum_{\sigma}\ \sum_{i}\mathrm{calls}(i,\sigma)\ \le\ \Big(\sum_{v}\binom{\deg v}{2}\Big)\, m!.$$
--   Equivalently, for a uniformly random ranking and a uniformly random edge, the oracle deciding whether that edge is in the random greedy maximal matching makes on average at most $\frac1m\sum_v\binom{\deg v}2\le \Delta-1$ recursive calls, where $\Delta$ is the maximum degree.
--
--   This bounds the query cost of the matching-size estimator used to estimate the conflict-cover cost in the sublinear metric TSP algorithm.
--
--   **Formalization Note** The number of edges of the line graph equals $\sum_v\binom{\deg v}2$ because two distinct edges of a simple graph share at most one endpoint.
-- source:
--   Dalirrooyfard–Makarychev–Mitrović, arXiv:2604.01462 (2026), Corollary 1.2, applied to the line graph; used for Lemma 9.9 of Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, p.40.

import Mathlib
import Definitions.Def_GraphMatching_basic
import Definitions.Def_RandomGreedyMIS_basic
import Definitions.Def_RandomGreedyMIS_matching

namespace RandomGreedyMIS

/-- **Query cost of the random greedy matching oracle.** Applying the average-case bound for the recursive random
greedy MIS oracle (Dalirrooyfard–Makarychev–Mitrović, arXiv:2604.01462, Corollary 1.2) to the line graph, whose number
of edges is `Σ_v C(deg v, 2)`: summed over all `m!` rankings of the edges and all edges, the oracle makes at most
`(Σ_v C(deg v, 2)) · m!` recursive calls. -/
theorem gmm_calls_le {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (∑ σ : Equiv.Perm (Fin H.edgeFinset.card), ∑ i, (calls (lineGraph H) σ i : ℝ)) ≤
      (∑ v : Fin n, ((H.degree v).choose 2 : ℝ)) * (Nat.factorial H.edgeFinset.card) := by sorry

end RandomGreedyMIS
