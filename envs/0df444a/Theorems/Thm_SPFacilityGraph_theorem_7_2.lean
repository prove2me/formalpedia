-- Prove2me | Theorems.Thm_SPFacilityGraph_theorem_7_2
-- name    : SPFacilityGraph.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:07:40.80992+00:00
-- url     : https://prove2.me/theorems/73b331d7-6670-4cb8-8f08-d48f6371f0d2
-- title:
--   Theorem 7.2 — a deterministic onto mechanism is SP iff SSP iff it has a deterministic PL attribution
-- statement:
--   Let $G \subseteq \mathbb R^k$ be a metric graph with straight edges, let $n \ge 2$ be the number of agents, and let $M : G^n \to G$ be a deterministic onto mechanism (every location of $G$ is the outcome at some profile). The following are equivalent:
--
--   1. $M$ is strategyproof: $d_G(M(\boldsymbol x), x_i) \le d_G(M(z, \boldsymbol x_{-i}), x_i)$ for all $\boldsymbol x$, $i$, $z$.
--   2. $M$ is strongly strategyproof: $d_G(M(y, \boldsymbol x_{-i}), t) \le d_G(M(z, \boldsymbol x_{-i}), t)$ whenever $d_G(t,z) = d_G(t,y) + d_G(y,z)$.
--   3. $M$ admits a deterministic PL $(\Pi(W), \mathcal T)$-attribution for some finite $W \subseteq G$ and some $\mathcal T$ satisfying the PL attribution assumptions: there are a finite triangulation of $G^n$ whose maximal simplices lie in products of graph edges and, for each maximal simplex $T$, a selector $f_T \in \Pi(W)$ (a report selector $\pi_i$ or a constant $\kappa_w$, $w \in W$) with $M = f_T$ on $T$.
--
--   The theorem shows that the piecewise-linear attribution representation loses nothing for deterministic mechanisms: every deterministic SP onto mechanism on a metric graph has a finite description by report and constant selectors on a triangulation, and satisfies the stronger, finitely checkable SSP condition.
--
--   **Formalization Note** The equivalence is a `List.TFAE` of the three clauses, for every $k$, every straight-edge metric graph and every surjective $M$.
--
--   Differences from the source:
--   - encoding: a graph: a connected compact subset of R^k (k a positive integer), a finite union of edges with distinct endpoints meeting only at common endpoints, at least one edge, every edge a straight segment (standing assumption of Section 3.2) → MetricGraph k: a nonempty Finset of ordered endpoint pairs (a, b), a ≠ b, edge = segment ℝ a b, two distinct edges intersect only in common endpoints, union connected; k ∈ ℕ; reason: the straight-edge assumption is the paper's standing assumption for Theorem 7.2; compactness, positive finite length and no self-intersection are automatic for finitely many straight segments; k = 0 admits no edge with distinct endpoints, so the instances are the same
--   - encoding: d_G(x, y) = min over paths (minimal connected subsets) of their length → MetricGraph.dist: infimum over finite walks x = p_0, …, p_m = y with consecutive points on a common edge segment of Σ‖p_j − p_{j−1}‖; reason: on a straight-edge graph every path is traced by such a walk of equal length and every walk contains a path of no greater length; same value
--   - encoding: a deterministic mechanism M : Gⁿ → Δ(G) with degenerate lotteries, cost(δ_y, x) = d_G(y, x) → M : Profile G n → G.Pt, cost d_G(M(𝒙), x); reason: the paper identifies each point with its point mass (p.4); same mechanisms and costs
--   - encoding: a deterministic PL (Π(W), T)-attribution: selectors Π(W), regions T the maximal simplices of a finite triangulation of Gⁿ inside edge products, affine mixing weights equal to 1 on one selector f_T and 0 on the others → IsEdgeTriangulation G n K (a finite Mathlib SimplicialComplex K with K.space = Gⁿ, every facet inside a product of edge segments) and HasDetAttribution G M W K (a selector of Π(W) per facet with M = selector on the closed facet); reason: constant 0/1 weights are affine, in [0, 1] and sum to 1, so (3.2) reduces to M = f_T on T; Π(W) consists of coordinate projections and constants, which are PL, and is finite and nonempty; Mathlib simplicial complexes are geometric triangulations (they omit only the empty face)
--   - encoding: onto: every location of G is an output at some profile → Function.Surjective M; reason: same condition
--   - encoding: agents N = {1, …, n} → Fin n (0-based); reason: relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Theorem 7.2, p.16 (restated p.49; proof p.52)

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP
import Definitions.Def_SPFacilityGraph_IsSSP
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution

set_option autoImplicit false

namespace SPFacilityGraph

/-- Theorem 7.2 (characterization of deterministic mechanisms) (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Theorem 7.2, p.16;
restated p.49, proof p.52).

Let `n ≥ 2`, let `G` be a (straight-edge) metric graph and let `M : Gⁿ → G` be a deterministic
onto mechanism. The following are equivalent:
1. `M` is SP;
2. `M` is SSP;
3. `M` admits a deterministic PL `(Π(W), T)`-attribution for some finite `W ⊆ G` and some `T`
   satisfying the PL attribution assumptions of Section 3.3 (the maximal simplices of a finite
   triangulation of `Gⁿ`, each inside a product of edges).

**Formalization Note** Onto is `Function.Surjective M`. Clause 3 is a finite `W`, a Mathlib
simplicial complex `K` with `IsEdgeTriangulation`, and a selector of `Π(W)` per maximal simplex
agreeing with `M` there (`HasDetAttribution`). -/
theorem theorem_7_2 {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (M : Profile G n → G.Pt) (hM : Function.Surjective M) :
    List.TFAE [IsSP G M, IsSSP G M,
      ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
        IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K] := by sorry

end SPFacilityGraph
