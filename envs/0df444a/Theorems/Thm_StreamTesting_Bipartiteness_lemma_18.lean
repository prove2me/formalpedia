-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_lemma_18
-- name    : StreamTesting.Bipartiteness.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:59:08.034194+00:00
-- url     : https://prove2.me/theorems/d6c82a73-f883-45f8-a881-447c420db3c8
-- title:
--   Lemma 18 — exact transcript-labeling count equality
-- statement:
--   Fix a finite simple base graph $H$ on $m$ vertices, any deterministic forward-only policy $A$, any arrival order $\sigma$ of the $2m$ observed labels, and any complete transcript $T$. Then
--
--   $$\bigl|\{\Lambda:T^{A,\sigma}_{0,\Lambda}=T,\ \pi_\Lambda(T)\text{ bipartite}\}\bigr|
--   =\bigl|\{\Lambda:T^{A,\sigma}_{1,\Lambda}=T,\ \pi_\Lambda(T)\text{ bipartite}\}\bigr|.$$
--
--   Each set counts actual bijections $\Lambda:[2m]\to V(H)\times\{0,1\}$ producing the indicated transcript under the actual execution. Impossible transcripts contribute zero. This equality identifies the part of the transcript laws whose projected revealed subgraph is bipartite.
--
--   Differences from the source:
--   - encoding: finite simple graphs on [n], with n/2 base vertices → SimpleGraph (Fin n); base graphs on Fin m and lifts on Fin m × Bool with n = 2m; reason: zero-based relabeling preserves all graphs, unordered edges, arrival permutations, and the exact normalization
--   - encoding: deterministic forward-only neighborhood-query testers → arbitrary deterministic observed-history decision tables with actual recursive execution; reason: the current label and prior observed history determine every decision; arbitrary tables preserve unrestricted memory, computation, and adaptivity
--   - generalization: the base graph H selected in §4.1 → every finite simple H, without connectedness, regularity, high girth, or farness; reason: the coloring-and-bit-swap pairing on pp.22–23 uses only the graph lift and bipartiteness of the actual projection, and hence includes the source family
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 18, printed p.22 / PDF p.22; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_Projection
import Definitions.Def_StreamTesting_Bipartiteness_Execution
import Definitions.Def_StreamTesting_Bipartiteness_Bipartite

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Lemma 18, p.22: exact counts of actual bijections, for every transcript. -/
theorem lemma_18 {m : ℕ} (H : SimpleGraph (Fin m)) (A : Policy (2 * m))
    (σ : Order (2 * m)) (T : History (2 * m)) :
    Nat.card {Λ : Labeling m | execute (labeledGraph H false Λ) A σ = T ∧
      Bipartite (projection Λ T)} =
    Nat.card {Λ : Labeling m | execute (labeledGraph H true Λ) A σ = T ∧
      Bipartite (projection Λ T)} := by sorry

end StreamTesting.Bipartiteness
