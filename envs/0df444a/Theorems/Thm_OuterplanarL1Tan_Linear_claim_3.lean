-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_claim_3
-- name    : OuterplanarL1Tan.Linear.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:13:56.896043+00:00
-- url     : https://prove2.me/theorems/eb76538c-f8e0-4831-a8f9-db3887078118
-- title:
--   Claim 3 — at most two cyclic boundary transitions
-- statement:
--   Let $H$ be a finite connected plane graph with nonnegative symmetric real edge lengths, and let $b_0,\ldots,b_{m-1}$ be its outer facial walk. For $x,y\in V(H)$ put $D=d_H(x,y)$, $q(z)=d_H(x,z)-d_H(y,z)$, and $A_t=\{z:q(z)\le t\}$. For every real threshold $-D<t<D$,
--
--   $$\#\{j\in\mathbb Z/m\mathbb Z:\mathbf1_{A_t}(b_j)\ne\mathbf1_{A_t}(b_{j+1})\}\le2.$$
--
--   The transitions count visits with multiplicity and include the closing step. This boundary nonalternation statement is the support used in the pattern bound. If $D=0$, the strict threshold interval is empty, exactly as in the source preamble.
--
--   **Formalization Note** Reachability supplies actual finite distances; the facial walk supplies the nonempty component and its geometric order. The statement does not assume connectedness of any residual of an ambient graph, nor any nonalternation conclusion in the drawing data.
--
--   Differences from the source:
--   - encoding: edge-weighted plane graph H with a shortest-path metric → an arbitrary Fintype vertex carrier, symmetric real edge lengths on SimpleGraph, and an actual walk for each pair; reason: the paper's graphs are finite (§3.3 applies the finite-X Lemma 6 to V(H)) and it mentions no loops or parallel edges; a disconnected H has no finite distances, so the source's objects are undefined there and actual-walk reachability spells this out
--   - generalization: shortest-path metrics → nonnegative real edge lengths allowing pseudometric coincidences; reason: every metric instance remains included; the distance-difference and localization arguments also apply to zero-length edges
--   - reading: boundary vertices in cyclic order in §2.1 → visits of the outer facial walk, including repetitions; reason: Appendix A explicitly uses the outer facial walk, which repeats articulation vertices and bridge endpoints
--   - encoding: the geometric cyclic outer facial walk → a traversal with a continuous exterior collar and at most one use of each oriented edge; reason: exterior regular neighbourhoods characterize the ordinary facial order; the witness contains no distance inequality and does not restrict the graph or its weights
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ₁, STOC 2027 submission #262 (October 2026), p. 3, 8, Claim 3 with its preamble and Appendix A (PDF p. 4, 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf; SHA256 0ec64e77e85f536fdf7dc42bb8fdeedaf8861f751861d02b2d5edbdef75ee0ab

import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern

namespace OuterplanarL1Tan.Linear

/-- Claim 3, printed p.3 (PDF p.4), with its threshold preamble;
Appendix A explicitly uses the outer facial walk, including repeated visits. -/
theorem claim_3 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) (t : ℝ)
    (lower : -W.distance x y < t) (upper : t < W.distance x y) :
    transitionCount D B (sublevel W x y t) ≤ 2 := by sorry

end OuterplanarL1Tan.Linear
