-- Prove2me | Theorems.Thm_SPFacilityGraph_lemma_Q_3
-- name    : SPFacilityGraph.lemma_Q_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:05:28.799665+00:00
-- url     : https://prove2.me/theorems/5d27979c-6a20-49e4-badb-f8ff00919589
-- title:
--   Lemma Q.3 — representation on a line segment
-- statement:
--   Let $G = [0, L]$ with $L > 0$ and $n \ge 2$. Every deterministic strategyproof onto mechanism $M : G^n \to G$ admits a deterministic PL $(\Pi(W), \mathcal T)$-attribution for some finite $W \subseteq G$ and some finite triangulation of $G^n$ whose maximal simplices form a family $\mathcal T$ satisfying the PL attribution assumptions: each maximal simplex lies in a product of edges, and on each maximal simplex $T$ the mechanism coincides with one selector $f_T \in \Pi(W)$, a report selector or a constant at a point of $W$.
--
--   This is the segment case of the implication (1) ⇒ (3) of Theorem 7.2.
--
--   Differences from the source:
--   - generalization: G = [0, L] ⊆ ℝ with L > 0 → any MetricGraph k whose carrier is a segment [p, q] ⊆ ℝ^k (any subdivision into edges), arclength coordinate ‖x − p‖ and L = ‖q − p‖; the hypothesis L > 0 is not stated; reason: [0, L] with any set of vertices is the case k = 1, p = 0, q = L; L > 0 follows from the graph having an edge with distinct endpoints, so the dropped hypothesis excludes nothing
--   - encoding: d_G(x, y) = min over paths (minimal connected subsets) of their length → MetricGraph.dist: infimum over finite walks x = p_0, …, p_m = y with consecutive points on a common edge segment of Σ‖p_j − p_{j−1}‖; reason: on a straight-edge graph every path is traced by such a walk of equal length and every walk contains a path of no greater length; same value
--   - encoding: a deterministic mechanism M : Gⁿ → Δ(G) with degenerate lotteries, cost(δ_y, x) = d_G(y, x) → M : Profile G n → G.Pt, cost d_G(M(𝒙), x); reason: the paper identifies each point with its point mass (p.4); same mechanisms and costs
--   - encoding: a deterministic PL (Π(W), T)-attribution: selectors Π(W), regions T the maximal simplices of a finite triangulation of Gⁿ inside edge products, affine mixing weights equal to 1 on one selector f_T and 0 on the others → IsEdgeTriangulation G n K (a finite Mathlib SimplicialComplex K with K.space = Gⁿ, every facet inside a product of edge segments) and HasDetAttribution G M W K (a selector of Π(W) per facet with M = selector on the closed facet); reason: constant 0/1 weights are affine, in [0, 1] and sum to 1, so (3.2) reduces to M = f_T on T; Π(W) consists of coordinate projections and constants, which are PL, and is finite and nonempty; Mathlib simplicial complexes are geometric triangulations (they omit only the empty face)
--   - encoding: onto: every location of G is an output at some profile → Function.Surjective M; reason: same condition
--   - encoding: agents N = {1, …, n} → Fin n (0-based); reason: relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma Q.3, p.50

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution

set_option autoImplicit false

namespace SPFacilityGraph

/-- Lemma Q.3 (representation on a line segment) (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma Q.3, p.50).

Let `G = [0, L]` with `L > 0`, and `n ≥ 2`. Every deterministic SP onto mechanism
`M : Gⁿ → G` admits a deterministic PL `(Π(W), T)`-attribution for some finite `W ⊆ G` and some
finite triangulation of `Gⁿ` whose maximal simplices (the family `T`) lie in products of edges.

**Formalization Note** Generalized from `[0, L] ⊆ ℝ` to every metric graph whose carrier is a
segment `[p, q] ⊆ ℝ^k`, with any subdivision into edges. -/
theorem lemma_Q_3 {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K := by sorry

end SPFacilityGraph
