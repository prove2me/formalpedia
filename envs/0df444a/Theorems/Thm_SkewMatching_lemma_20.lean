-- Prove2me | Theorems.Thm_SkewMatching_lemma_20
-- name    : SkewMatching.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:34.363767+00:00
-- url     : https://prove2.me/theorems/4ef74c25-4ef8-49a2-aba4-ab1baa22ab91
-- title:
--   Lemma 20 — the charge of a non-barrier edge is a difference of vertex heights
-- statement:
--   Let $(A,A',X_1,\dots,X_k,M)$ be a barrier of a sub-multigraph $H$ of a finite skew-symmetric graph $G$, and let $K$ be a parameter. For every edge $e=(u,v)$ of $G$ that is neither a barrier edge $e_i$ or $e_i'$ nor has both ends in one small fragment,
--
--   $$
--   d_e=h(u^L)-h(v^R).
--   $$
--
--   Moreover every height $h(u^L)$, $h(u^R)$ lies in $\{-1,0,1\}$.
--
--   This reduces sampling by $|d_e|$ to sampling by height difference, which Lemma 21 reduces to sampling from a cut.
--
--   Differences from the source:
--   - generalization: G the current residual graph and the barrier found by the algorithm → every finite SkewGraph G and every barrier of a σ-closed H; reason: the proof uses only that the partition is a barrier
--   - reading: the lemma states only the identity → also: the heights lie in {−1, 0, 1}; reason: Lemma 21 is applied to these heights and needs this; the paper uses it there without stating it
--   - encoding: the auxiliary bipartite graph G₁ → the heights heightL and heightR on V; reason: G₁ has an edge (u^L, v^R) for each edge (u, v), so the identity needs nothing else of G₁
--   - reading: not in a small fragment X_i → not with both ends in one small fragment; reason: the proof's step 1[e ∈ ∂X_i] = 1[u ∈ X_i] + 1[v ∈ X_i] needs exactly this
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 20, p.13

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_charge

namespace SkewMatching

/-- **Lemma 20**, p.13. "For any edge e = (u, v) in G that is not any of the barrier edge e_i from A to each X_i and e′_i from each X_i to A′, and not in a small fragment X_i, the charge d_e can be written as the difference of vertex heights in G₁, i.e. d_e = h(u^L) − h(v^R)." with
`h(u^L) = ϕ(u) − 1[u ∈ X_i, |X_i| ≤ 2n/K]`, `h(u^R) = ϕ(u) + 1[u ∈ X_i, |X_i| ≤ 2n/K]`. The heights also lie in `{−1, 0, 1}`, which Lemma 21 needs.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 20, p.13.

**Formalization Note.** "In a small fragment" means both ends in one small fragment. The bipartite graph `G₁` has an edge `(u^L, v^R)` for each edge `(u, v)`, so its heights are `heightL`, `heightR`, and it needs no separate object. -/
theorem lemma_20 {V E : Type*} [Fintype V] [Fintype E] (G : SkewGraph V E) (H : Finset E)
    (hH : G.SymmClosed H) (s : V) (P : Partition V) (hP : G.IsBarrier H s P) (K : ℕ) :
    (∀ e : E, (∀ X ∈ P.frags, ¬ G.IsBarrierEdgeAt H P X e) →
        (¬ ∃ X ∈ P.frags, SkewGraph.IsSmall K X ∧ G.tail e ∈ X ∧ G.head e ∈ X) →
        G.charge K H P e = G.heightL K P (G.tail e) - G.heightR K P (G.head e)) ∧
      ∀ u : V, (G.heightL K P u = -1 ∨ G.heightL K P u = 0 ∨ G.heightL K P u = 1) ∧
        (G.heightR K P u = -1 ∨ G.heightR K P u = 0 ∨ G.heightR K P u = 1) := by sorry

end SkewMatching
