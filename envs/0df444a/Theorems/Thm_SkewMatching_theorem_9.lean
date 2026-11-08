-- Prove2me | Theorems.Thm_SkewMatching_theorem_9
-- name    : SkewMatching.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:38.945771+00:00
-- url     : https://prove2.me/theorems/72da8010-8794-4b5b-8cf1-d1464f281b2e
-- title:
--   Theorem 9 — a regular path exists iff no barrier exists
-- statement:
--   Let $H$ be a $\sigma$-closed set of edges of a finite skew-symmetric graph and let $s$ be a vertex. Then
--
--   $$
--   \text{there is a regular path from } s \text{ to } s' \text{ in } H \iff \text{there is no barrier from } s \text{ to } s' \text{ of } H.
--   $$
--
--   This is the analogue, for regular paths, of the statement that a cut certifies the absence of an augmenting path. It is what makes the barrier a stopping certificate for the search. The paper cites it to Goldberg and Karzanov.
--
--   Differences from the source:
--   - encoding: a skew-symmetric graph → a σ-closed edge set H of a finite SkewGraph; reason: a σ-closed edge set is itself a skew-symmetric multigraph, and H = all edges gives the whole graph
--   - encoding: a path → a vertex-simple path; reason: a regular walk contains a vertex-simple regular path, so existence is unchanged
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 9, p.4 (cited to [GK96])

import Mathlib
import Definitions.Def_SkewMatching_Partition

namespace SkewMatching

/-- **Theorem 9**, p.4. "A regular path from s to s′ exists if and only if no barrier from s to s′ exists."

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Theorem 9, p.4 (cited to [GK96], no proof in the paper).

**Formalization Note.** For every finite skew-symmetric multigraph, presented as a `σ`-closed edge set `H` of a `SkewGraph`, and every vertex `s`. Taking `H` to be all edges gives a whole
`SkewGraph`, and a `σ`-closed `H` is itself a skew-symmetric multigraph. Both directions. -/
theorem theorem_9 {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (H : Finset E)
    (hH : G.SymmClosed H) (s : V) :
    (∃ p, G.IsRegularPathIn H s (G.σV s) p) ↔ ¬ ∃ P : Partition V, G.IsBarrier H s P := by sorry

end SkewMatching
