-- Prove2me | Theorems.Thm_WeightedRainbowCycle_Weighted_density_expansion
-- name    : WeightedRainbowCycle.Weighted.density_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:25.111066+00:00
-- url     : https://prove2.me/theorems/7e1c0db8-10db-412a-8de4-d8ab327c0f3f
-- title:
--   Lemma 4.1 — logarithmic-density maximizer expands
-- statement:
--   Let $G$ be a finite loopless weighted list graph with nonnegative real weights, and let $H$ maximize $d(H)/\log|V(H)|$ over its subgraphs with at least two vertices. Set $n=|V(H)|$. For every nonempty vertex subset $S\subseteq V(H)$, including $S=V(H)$,
--
--   $$\frac{|\partial_H S|_w}{|S|}\ge\frac{d(H)}{2\log n}\log\frac{n}{|S|}.$$
--
--   Here $d(H)$ is twice inherited edge mass divided by $n$, and $|\partial_H S|_w$ counts each boundary edge's inherited weight once. This weighted expansion statement is the source's first supporting lemma for the main theorem. Lists do not enter the inequality; singleton dummy labels recover every uncolored instance.
--
--   Differences from the source:
--   - generalization: unweighted degree and boundary cardinality → nonnegative real weighted degree and boundary mass; reason: unit weights recover the full printed lemma; its edge-mass decomposition is unchanged
--   - generalization: graphs in the usual simple-graph reading → loopless finite multigraphs with distinct edge identities and length-two cycles allowed; reason: every simple graph embeds unchanged; weighted edge-counting arguments also retain parallel edges
--   - encoding: a subgraph maximizing d(H)/log |V(H)| with n implicit → genuine vertex-and-edge subgraphs and n = card V(H) ≥ 2, maximizing over all such nontrivial subgraphs; reason: excludes only undefined logarithmic denominators; singleton induced subgraphs have zero degree, and all nonempty S remain covered
--   - encoding: finite vertices and edges, with an arbitrary color set → finite vertex and edge types, finite edge lists, and an arbitrary ambient color type; reason: these represent every finite input graph and every finite list without restricting colors or real weights
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Lemma 4.1, p. 8; proof, p. 9 (also Lemma 2.2, p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_WeightedRainbowCycle_Weighted_Subgraph

set_option autoImplicit false

namespace WeightedRainbowCycle.Weighted

/-- Lemma 4.1, p. 8, with inherited nonnegative weights and parallel edges. -/
theorem density_expansion {V E C : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    (G : Model V E C) (H : Subgraph G) (hmax : H.IsDensityMax)
    (S : Finset V) (hS : S.Nonempty) (hSH : S ⊆ H.verts) :
    H.degree / (2 * Real.log H.verts.card) * Real.log ((H.verts.card : ℝ) / S.card) ≤
      H.boundaryMass S / S.card := by sorry

end WeightedRainbowCycle.Weighted
