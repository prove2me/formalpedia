-- Prove2me | Theorems.Thm_SPFacilityGraph_attribution_of_lipschitz
-- name    : SPFacilityGraph.attribution_of_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:48:03.296138+00:00
-- url     : https://prove2.me/theorems/7df74f65-9785-5dfc-8395-9823a62ae3d0
-- title:
--   Deterministic PL attribution from Lipschitz reports and finitely many non-report values
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph with graph distance $d_G$, let $n\ge 0$, and let $M:G^n\to G$ be a deterministic mechanism. Suppose that
--
--   1. $M$ is $1$-Lipschitz in each report: for every profile $\boldsymbol x\in G^n$, every agent $i$ and every $y\in G$,
--   $$
--   d_G\big(M(y,\boldsymbol x_{-i}),\,M(\boldsymbol x)\big)\;\le\; d_G(y,x_i);
--   $$
--   2. there is a finite set $W\subseteq G$ such that every outcome is a report or a point of $W$: for every $\boldsymbol x$, either $M(\boldsymbol x)=x_i$ for some agent $i$, or $M(\boldsymbol x)\in W$.
--
--   Then $M$ admits a deterministic PL $(\Pi(W),\mathcal T)$-attribution: there is a finite triangulation $K$ of $G^n\subseteq(\mathbb R^k)^n$ whose maximal simplices each lie in a product $e_1\times\dots\times e_n$ of edges, and a choice of one selector $f_T\in\Pi(W)$ (a report selector $\pi_i$ or a constant $\kappa_w$, $w\in W$) for every maximal simplex $T$, with $M=f_T$ on $T$.
--
--   This isolates the triangulation step of the source's proofs of Lemmas Q.3 and Q.4: once a deterministic SP onto mechanism is known to be Lipschitz in each report and to take only finitely many non-report values, it has a deterministic PL attribution with selectors in $\Pi(W)$. The triangulation refines the edges at the points of $W$ and triangulates each product of sub-edges by the Kuhn (Freudenthal) subdivision, which refines all order relations among reports on a common sub-edge.
--
--   **Formalization Note** The triangulation is a Mathlib `Geometry.SimplicialComplex` satisfying `IsEdgeTriangulation`, and the attribution is `HasDetAttribution G M W K`. The Lipschitz hypothesis is stated with the graph distance $d_G$ (an infimum of walk lengths), not the Euclidean distance.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092, proofs of Lemma Q.3 (p.50: "Subdivide the products of graph edges by the hyperplanes x_i = x_j and x_i = t_S ... Choose a finite triangulation refining these cells") and Lemma Q.4 (pp.51-52); triangulation of products of segments: Rourke–Sanderson, Introduction to Piecewise-Linear Topology, 1982

import Mathlib
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution
import Definitions.Def_SPFacilityGraph_MetricGraph_dist

set_option autoImplicit false

namespace SPFacilityGraph

theorem attribution_of_lipschitz {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt)
    (W : Finset G.Pt)
    (hLip : ∀ (x : Profile G n) (i : Fin n) (y : G.Pt),
      G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i))
    (hval : ∀ x : Profile G n, (∃ i, M x = x i) ∨ M x ∈ W) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k)),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K := by sorry

end SPFacilityGraph
