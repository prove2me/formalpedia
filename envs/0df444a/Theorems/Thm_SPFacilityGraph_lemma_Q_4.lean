-- Prove2me | Theorems.Thm_SPFacilityGraph_lemma_Q_4
-- name    : SPFacilityGraph.lemma_Q_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:04:34.420009+00:00
-- url     : https://prove2.me/theorems/e622a07f-2407-49ac-bdff-d6c35ab1acca
-- title:
--   Lemma Q.4 — representation on general graphs
-- statement:
--   Let $G$ be a straight-edge metric graph and $n \ge 2$. Every deterministic strategyproof onto mechanism $M : G^n \to G$ admits a deterministic PL $(\Pi(W), \mathcal T)$-attribution for some finite $W \subseteq G$ and some finite triangulation of $G^n$ whose maximal simplices form a family $\mathcal T$ satisfying the PL attribution assumptions: each maximal simplex lies in a product $e_1 \times \dots \times e_n$ of edges, and on each maximal simplex $T$ the mechanism coincides with one selector $f_T \in \Pi(W)$.
--
--   This is the implication (1) ⇒ (3) of Theorem 7.2, for trees and for graphs containing cycles.
--
--   Differences from the source:
--   - encoding: a graph: a connected compact subset of R^k (k a positive integer), a finite union of edges with distinct endpoints meeting only at common endpoints, at least one edge, every edge a straight segment (standing assumption of Section 3.2) → MetricGraph k: a nonempty Finset of ordered endpoint pairs (a, b), a ≠ b, edge = segment ℝ a b, two distinct edges intersect only in common endpoints, union connected; k ∈ ℕ; reason: the straight-edge assumption is the paper's standing assumption for Theorem 7.2; compactness, positive finite length and no self-intersection are automatic for finitely many straight segments; k = 0 admits no edge with distinct endpoints, so the instances are the same
--   - encoding: d_G(x, y) = min over paths (minimal connected subsets) of their length → MetricGraph.dist: infimum over finite walks x = p_0, …, p_m = y with consecutive points on a common edge segment of Σ‖p_j − p_{j−1}‖; reason: on a straight-edge graph every path is traced by such a walk of equal length and every walk contains a path of no greater length; same value
--   - encoding: a deterministic mechanism M : Gⁿ → Δ(G) with degenerate lotteries, cost(δ_y, x) = d_G(y, x) → M : Profile G n → G.Pt, cost d_G(M(𝒙), x); reason: the paper identifies each point with its point mass (p.4); same mechanisms and costs
--   - encoding: a deterministic PL (Π(W), T)-attribution: selectors Π(W), regions T the maximal simplices of a finite triangulation of Gⁿ inside edge products, affine mixing weights equal to 1 on one selector f_T and 0 on the others → IsEdgeTriangulation G n K (a finite Mathlib SimplicialComplex K with K.space = Gⁿ, every facet inside a product of edge segments) and HasDetAttribution G M W K (a selector of Π(W) per facet with M = selector on the closed facet); reason: constant 0/1 weights are affine, in [0, 1] and sum to 1, so (3.2) reduces to M = f_T on T; Π(W) consists of coordinate projections and constants, which are PL, and is finite and nonempty; Mathlib simplicial complexes are geometric triangulations (they omit only the empty face)
--   - encoding: onto: every location of G is an output at some profile → Function.Surjective M; reason: same condition
--   - encoding: agents N = {1, …, n} → Fin n (0-based); reason: relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma Q.4, p.50 (proof pp.51–52)

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution

set_option autoImplicit false

namespace SPFacilityGraph

/-- Lemma Q.4 (representation on general graphs) (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma Q.4, p.50; proof pp.51–52).

Let `n ≥ 2` and let `G` be any (straight-edge) metric graph. Every deterministic SP onto mechanism
`M : Gⁿ → G` admits a deterministic PL `(Π(W), T)`-attribution for some finite `W ⊆ G` and some
finite triangulation of `Gⁿ` whose maximal simplices (the family `T`) lie in products of edges. -/
theorem lemma_Q_4 {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K := by sorry

end SPFacilityGraph
