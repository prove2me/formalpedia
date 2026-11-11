-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_lemma_21
-- name    : StreamTesting.Bipartiteness.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:49.086089+00:00
-- url     : https://prove2.me/theorems/f54ed0eb-ead7-4c29-b5c9-07348fee772d
-- title:
--   Lemma 21 — probability that a fixed lifted set consists of roots
-- statement:
--   Let $H$ be a finite simple graph on $m>0$ vertices with maximum degree at most $d$, put $n=2m$, and let $A$ be a deterministic forward-only tester using at most $q$ queries in the worst case. Suppose $(d+1)q\le n/2$. For either $s\in\{0,1\}$ and every fixed set $S\subseteq V(H)\times\{0,1\}$ of $k=|S|$ distinct lifted vertices,
--
--   $$\Pr_{(\Lambda,\sigma)\sim D_s}[S\subseteq R]\le\left(\frac{2q}{n}\right)^k.$$
--
--   Here $R$ is computed from the actual execution and the independent uniform labeling and order. The statement includes $q=0$ and $S=\varnothing$, uses neither event $E$ nor a forest premise, and assumes no independence between root events.
--
--   Differences from the source:
--   - encoding: finite simple graphs on [n], with n/2 base vertices → SimpleGraph (Fin n); base graphs on Fin m and lifts on Fin m × Bool with n = 2m; reason: zero-based relabeling preserves all graphs, unordered edges, arrival permutations, and the exact normalization
--   - encoding: deterministic forward-only neighborhood-query testers → arbitrary deterministic observed-history decision tables with actual recursive execution; reason: the current label and prior observed history determine every decision; arbitrary tables preserve unrestricted memory, computation, and adaptivity
--   - generalization: the fixed connected regular high-girth far base graph H → any nonempty finite H of maximum degree at most d; reason: the deferred-labeling proof on pp.25–26 uses only the degree upper bound, uniform bijections and the worst-case cap; all source family graphs satisfy these premises
--   - encoding: a fixed set S of k vertices and (d+1)q ≤ n/2 → a Finset S of distinct lifted vertices with exponent S.card and (d+1)q ≤ m; reason: n is exactly 2m; finite sets retain k=0 and roots with coincident projections
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 21, printed p.25 / PDF p.25; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_Roots
import Definitions.Def_StreamTesting_Bipartiteness_Tester

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Lemma 21, p.25: the probability is the actual independent labeling/order experiment.
S is fixed before the experiment, including the empty set. -/
theorem lemma_21 {m : ℕ} (hm : 0 < m) (H : SimpleGraph (Fin m)) (d q : ℕ)
    (hdegree : GreedyColoringLCA969.LowerBound.MaxDegreeAtMost H d) (A : Policy (2 * m))
    (hcap : DetQueryCap d A q) (hbudget : (d + 1) * q ≤ m)
    (s : Bool) (S : Finset (Fin m × Bool)) :
    PunctSketch.coinProb (fun ω : Labeling m × Order (2 * m) =>
      S ⊆ roots ω.1 (execute (labeledGraph H s ω.1) A ω.2)) ≤
      (2 * (q : ℝ) / (2 * (m : ℝ))) ^ S.card := by sorry

end StreamTesting.Bipartiteness
