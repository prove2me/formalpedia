-- Prove2me | Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
-- name    : SPFacilityGraph.MetricGraph.exists_walk_eq_dist
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:11:15.478103+00:00
-- url     : https://prove2.me/theorems/4d010886-9666-4fb8-a860-9ffa05c4d3e3
-- title:
--   Shortest walks exist in a metric graph
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph and let $x,y\in G$. Then the graph distance $d_G(x,y)$ is attained by a walk: there are $m\in\mathbb N$ and points $x=p_0,p_1,\dots,p_m=y$ such that every two consecutive points $p_j,p_{j+1}$ lie on a common edge segment of $G$ and
--
--   $$
--   \sum_{j=0}^{m-1}\|p_{j+1}-p_j\| \;=\; d_G(x,y).
--   $$
--
--   In the source, $d_G(x,y)$ is "the minimum length of a path in $G$ between $x$ and $y$"; this statement says that the infimum over walks used to define $d_G$ is indeed a minimum, so shortest polygonal paths exist. It is the starting point of every argument that splits a shortest path into pieces, such as the locality theorem for strong strategyproofness (Theorem 4.5).
--
--   **Formalization Note** A walk is a function $p:\mathbb N\to\mathbb R^k$ together with a number of steps $m$; values $p_j$ with $j>m$ are irrelevant.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092, Section 2.1, p.4 (graph distance d_G: the minimum length of a path in G; a metric on G)

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist

set_option autoImplicit false

namespace SPFacilityGraph

theorem MetricGraph.exists_walk_eq_dist {k : ℕ} (G : MetricGraph k) (x y : G.Pt) :
    ∃ (m : ℕ) (p : ℕ → EuclideanSpace ℝ (Fin k)), p 0 = x ∧ p m = y ∧
      (∀ j < m, ∃ e ∈ G.edges, p j ∈ segment ℝ e.1 e.2 ∧ p (j + 1) ∈ segment ℝ e.1 e.2) ∧
      ∑ j ∈ Finset.range m, ‖p (j + 1) - p j‖ = G.dist x y := by sorry

end SPFacilityGraph
