-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_lemma_5
-- name    : OuterplanarL1Tan.Linear.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:14:57.506106+00:00
-- url     : https://prove2.me/theorems/cf412339-53f0-40ff-a6d0-ad1850fc34fb
-- title:
--   Lemma 5 — fine separation of the fixed augmented map
-- statement:
--   Let $H$ be a finite connected plane weighted graph with boundary $B=\partial H$ in its inherited drawing. Write $d_H$ for its intrinsic shortest-path distance, let $\Phi_H$ be its boundary pattern, and set $g_H(z)=\tfrac14\Phi_H(z)\oplus2d_H(z,B)$. For all $x,y\in V(H)$,
--
--   $$\|g_H(x)-g_H(y)\|_1\ge d_H(x,y)-4\min\{d_H(x,B),d_H(y,B)\}.$$
--
--   This is the full separation estimate even when its right side is negative. Neither endpoint is required to lie on the boundary. The same statement applies to every connected component of an arbitrary residual graph, with its own boundary and intrinsic distance.
--
--   **Formalization Note** The augmented map is the defined graph-dependent map, in an ℓ₁ direct sum. It is not a free map satisfying an asserted bound. There is no hypothesis equating intrinsic and ambient distances.
--
--   Differences from the source:
--   - encoding: edge-weighted plane graph H with a shortest-path metric → an arbitrary Fintype vertex carrier, symmetric real edge lengths on SimpleGraph, and an actual walk for each pair; reason: the paper's graphs are finite (§3.3 applies the finite-X Lemma 6 to V(H)) and it mentions no loops or parallel edges; a disconnected H has no finite distances, so the source's objects are undefined there and actual-walk reachability spells this out
--   - generalization: shortest-path metrics → nonnegative real edge lengths allowing pseudometric coincidences; reason: every metric instance remains included; the distance-difference and localization arguments also apply to zero-length edges
--   - reading: boundary vertices in cyclic order in §2.1 → visits of the outer facial walk, including repetitions; reason: Appendix A explicitly uses the outer facial walk, which repeats articulation vertices and bridge endpoints
--   - encoding: the geometric cyclic outer facial walk → a traversal with a continuous exterior collar and at most one use of each oriented edge; reason: exterior regular neighbourhoods characterize the ordinary facial order; the witness contains no distance inequality and does not restrict the graph or its weights
--   - reading: H_i and L_i in the displayed statement of Lemma 5 → a connected plane graph H and its own outer boundary ∂H; reason: §3.3 explicitly applies this map and estimate separately to each connected residual component; no distance is asserted between disconnected components
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 4, 7, Lemma 5 and its componentwise use in §3.3 (PDF p. 5, 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern

namespace OuterplanarL1Tan.Linear

/-- Lemma 5, printed p.4 (PDF p.5), used for each connected residual
component with its own inherited drawing in §3.3. No ambient isometry assumed. -/
theorem lemma_5 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) :
    W.distance x y - 4 * min (boundaryDistance W D x) (boundaryDistance W D y) ≤
      ‖augmented W D B x - augmented W D B y‖ := by sorry

end OuterplanarL1Tan.Linear
