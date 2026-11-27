-- Prove2me | Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
-- name    : SPFacilityGraph.MetricGraph.dist_le_walk
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:11:27.8592+00:00
-- url     : https://prove2.me/theorems/86193c4e-7077-5696-a42a-160e9a3c381a
-- title:
--   Graph distance is at most the length of any walk
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph and let $x,y\in G$. Suppose $x=p_0,p_1,\dots,p_m=y$ is a **walk** in $G$: for every $j<m$ the consecutive points $p_j$ and $p_{j+1}$ lie on a common edge segment $[a,b]$ of $G$. Then the graph distance is bounded by the polygonal length of the walk:
--
--   $$
--   d_G(x,y)\;\le\;\sum_{j=0}^{m-1}\|p_{j+1}-p_j\|.
--   $$
--
--   This is the basic upper bound coming from the definition of $d_G$ as the infimum of walk lengths; it is the tool used to bound graph distances by explicit walks (concatenations, reversals, sub-walks).
--
--   **Formalization Note** A walk is a function $p:\mathbb N\to\mathbb R^k$ together with a number of steps $m$; values $p_j$ with $j>m$ are irrelevant. The case $m=0$ is allowed (then $x=y$).
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092, Section 2.1, p.4 (graph distance d_G: the minimum length of a path in G; a metric on G)

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist

set_option autoImplicit false

namespace SPFacilityGraph

theorem MetricGraph.dist_le_walk {k : ℕ} (G : MetricGraph k) (x y : G.Pt) (m : ℕ)
    (p : ℕ → EuclideanSpace ℝ (Fin k)) (h0 : p 0 = x) (hm : p m = y)
    (hw : ∀ j < m, ∃ e ∈ G.edges, p j ∈ segment ℝ e.1 e.2 ∧ p (j + 1) ∈ segment ℝ e.1 e.2) :
    G.dist x y ≤ ∑ j ∈ Finset.range m, ‖p (j + 1) - p j‖ := by sorry

end SPFacilityGraph
