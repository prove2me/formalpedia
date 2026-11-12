-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_lemma_2
-- name    : OuterplanarL1Tan.Linear.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:14:32.246271+00:00
-- url     : https://prove2.me/theorems/6085ef47-c33b-4fb5-96c6-230833196dd4
-- title:
--   Lemma 2 — pattern expansion and exact boundary equality
-- statement:
--   Let $H$ be a finite connected plane weighted graph, with outer facial walk $b_0,\ldots,b_{m-1}$ and intrinsic shortest-path distance $d_H$. Define $\Phi_H(z)_j=d_H(z,b_j)-d_H(z,b_{j+1})$. Both conclusions hold:
--
--   $$\|\Phi_H(x)-\Phi_H(y)\|_1\le4d_H(x,y)\qquad(x,y\in V(H)),$$
--   $$\|\Phi_H(x)-\Phi_H(y)\|_1=4d_H(x,y)\qquad(x,y\in\partial H).$$
--
--   This states the global expansion estimate and the full equality clause for every boundary pair. It does not replace equality by a noncontraction inequality. Repeated boundary visits, bridges, singleton components and zero-distance pairs are retained.
--
--   **Formalization Note** The vector space is `PiLp 1`, so its norm sums coordinate absolute values. This standalone result has no hypothesis that a residual preserves distances in an ambient graph; all distances are intrinsic to $H$.
--
--   Differences from the source:
--   - encoding: edge-weighted plane graph H with a shortest-path metric → an arbitrary Fintype vertex carrier, symmetric real edge lengths on SimpleGraph, and an actual walk for each pair; reason: the paper's graphs are finite (§3.3 applies the finite-X Lemma 6 to V(H)) and it mentions no loops or parallel edges; a disconnected H has no finite distances, so the source's objects are undefined there and actual-walk reachability spells this out
--   - generalization: shortest-path metrics → nonnegative real edge lengths allowing pseudometric coincidences; reason: every metric instance remains included; the distance-difference and localization arguments also apply to zero-length edges
--   - reading: boundary vertices in cyclic order in §2.1 → visits of the outer facial walk, including repetitions; reason: Appendix A explicitly uses the outer facial walk, which repeats articulation vertices and bridge endpoints
--   - encoding: the geometric cyclic outer facial walk → a traversal with a continuous exterior collar and at most one use of each oriented edge; reason: exterior regular neighbourhoods characterize the ordinary facial order; the witness contains no distance inequality and does not restrict the graph or its weights
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 3, Lemma 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern

namespace OuterplanarL1Tan.Linear

/-- Lemma 2, printed p.3 (PDF p.4): both the bound and boundary equality. -/
theorem lemma_2 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) :
    (∀ x y : V, ‖pattern W D B x - pattern W D B y‖ ≤ 4 * W.distance x y) ∧
    (∀ x y : V, x ∈ D.boundary Set.univ → y ∈ D.boundary Set.univ →
      ‖pattern W D B x - pattern W D B y‖ = 4 * W.distance x y) := by sorry

end OuterplanarL1Tan.Linear
