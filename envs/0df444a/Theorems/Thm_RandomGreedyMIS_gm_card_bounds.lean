-- Prove2me | Theorems.Thm_RandomGreedyMIS_gm_card_bounds
-- name    : RandomGreedyMIS.gm_card_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:35:02.963104+00:00
-- url     : https://prove2.me/theorems/1642bc12-f2e7-50c5-9637-7ef4f1d8ceed
-- title:
--   Greedy maximal matching: $\nu/2\le|GM|\le\nu$
-- statement:
--   Let $H$ be a finite simple graph with matching number $\nu(H)$, and let $\sigma$ be any ranking of its edges. The greedy matching $GM(\sigma)$ — the edges whose vertex in the line graph belongs to the greedy maximal independent set for $\sigma$ — is a maximal matching of $H$, and therefore
--   $$\nu(H)\le 2\,|GM(\sigma)|\qquad\text{and}\qquad |GM(\sigma)|\le\nu(H).$$
--
--   Estimating $|GM(\sigma)|$ for a random ranking by sampling edges and running the local oracle thus gives a $2$-approximation of the maximum matching size; in the sublinear TSP algorithm this approximates the conflict-cover cost $\tau$.
-- source:
--   S. Behnezhad, Time-optimal sublinear algorithms for matching and vertex cover, FOCS 2021; Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, Lemma 9.9 and §9.2.2, p.40.

import Mathlib
import Definitions.Def_GraphMatching_basic
import Definitions.Def_RandomGreedyMIS_basic
import Definitions.Def_RandomGreedyMIS_matching

namespace RandomGreedyMIS

/-- **The random greedy matching is a maximal matching.** For every ranking `σ` of the edges, the greedy matching
`GM H σ` (greedy MIS of the line graph) is a matching of `H` meeting every edge, hence
`ν(H) ≤ 2 |GM H σ| ≤ 2 ν(H)`. This is the approximation guarantee of the randomized greedy maximal matching used by
the matching-size estimator (Behnezhad, FOCS 2021; Lemma 9.9 of Azarmehr–Behnezhad, arXiv:2611.04283, p.40). -/
theorem gm_card_bounds {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (σ : Equiv.Perm (Fin H.edgeFinset.card)) :
    GraphMatching.matchingNumber H ≤ 2 * (GM H σ).card ∧ (GM H σ).card ≤ GraphMatching.matchingNumber H := by sorry

end RandomGreedyMIS
