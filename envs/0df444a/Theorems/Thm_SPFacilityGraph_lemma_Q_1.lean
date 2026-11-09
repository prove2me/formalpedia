-- Prove2me | Theorems.Thm_SPFacilityGraph_lemma_Q_1
-- name    : SPFacilityGraph.lemma_Q_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:03:55.376789+00:00
-- url     : https://prove2.me/theorems/4604a8a1-1cab-4c0e-b5b6-9ae6a3c06ed5
-- title:
--   Lemma Q.1 — deterministic attributions with selectors in $\Pi(W)$ imply SSP
-- statement:
--   Let $G$ be a straight-edge metric graph, $W \subseteq G$ finite, and $K$ a finite triangulation of $G^n$ whose maximal simplices $T$ lie in products of graph edges. If a deterministic mechanism $M : G^n \to G$ agrees on each maximal simplex $T$ with a single selector $f_T \in \Pi(W)$ (a report selector $\pi_i$ or a constant $\kappa_w$, $w \in W$), then $M$ is strongly strategyproof.
--
--   In words: the mechanism represented by any deterministic PL $(\Pi(W), \mathcal T)$-attribution is SSP. This is the implication (3) ⇒ (2) of Theorem 7.2.
--
--   Differences from the source:
--   - generalization: n ≥ 2 agents (Section 2.2) → any n ∈ ℕ; reason: the proof does not use n ≥ 2
--   - encoding: a graph: a connected compact subset of R^k (k a positive integer), a finite union of edges with distinct endpoints meeting only at common endpoints, at least one edge, every edge a straight segment (standing assumption of Section 3.2) → MetricGraph k: a nonempty Finset of ordered endpoint pairs (a, b), a ≠ b, edge = segment ℝ a b, two distinct edges intersect only in common endpoints, union connected; k ∈ ℕ; reason: the straight-edge assumption is the paper's standing assumption for Theorem 7.2; compactness, positive finite length and no self-intersection are automatic for finitely many straight segments; k = 0 admits no edge with distinct endpoints, so the instances are the same
--   - encoding: d_G(x, y) = min over paths (minimal connected subsets) of their length → MetricGraph.dist: infimum over finite walks x = p_0, …, p_m = y with consecutive points on a common edge segment of Σ‖p_j − p_{j−1}‖; reason: on a straight-edge graph every path is traced by such a walk of equal length and every walk contains a path of no greater length; same value
--   - encoding: a deterministic mechanism M : Gⁿ → Δ(G) with degenerate lotteries, cost(δ_y, x) = d_G(y, x) → M : Profile G n → G.Pt, cost d_G(M(𝒙), x); reason: the paper identifies each point with its point mass (p.4); same mechanisms and costs
--   - encoding: a deterministic PL (Π(W), T)-attribution: selectors Π(W), regions T the maximal simplices of a finite triangulation of Gⁿ inside edge products, affine mixing weights equal to 1 on one selector f_T and 0 on the others → IsEdgeTriangulation G n K (a finite Mathlib SimplicialComplex K with K.space = Gⁿ, every facet inside a product of edge segments) and HasDetAttribution G M W K (a selector of Π(W) per facet with M = selector on the closed facet); reason: constant 0/1 weights are affine, in [0, 1] and sum to 1, so (3.2) reduces to M = f_T on T; Π(W) consists of coordinate projections and constants, which are PL, and is finite and nonempty; Mathlib simplicial complexes are geometric triangulations (they omit only the empty face)
--   - encoding: agents N = {1, …, n} → Fin n (0-based); reason: relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma Q.1, p.49

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSSP
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution

set_option autoImplicit false

namespace SPFacilityGraph

/-- Lemma Q.1 (deterministic attributions with selectors in `Π(W)` imply SSP) (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049),
Lemma Q.1, p.49).

For every finite `W ⊆ G` and every deterministic PL `(Π(W), T)`-attribution, the represented
mechanism is SSP: if `K` is a finite triangulation of `Gⁿ` whose maximal simplices lie in
products of edges and `M` agrees on each maximal simplex with one selector of `Π(W)`, then `M`
is SSP.

**Formalization Note** The represented mechanism `M_A` is the mechanism `M` of which the
attribution is one (`HasDetAttribution`). -/
theorem lemma_Q_1 {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt) (W : Finset G.Pt)
    (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k)))
    (hK : IsEdgeTriangulation G n K) (hA : HasDetAttribution G M W K) :
    IsSSP G M := by sorry

end SPFacilityGraph
