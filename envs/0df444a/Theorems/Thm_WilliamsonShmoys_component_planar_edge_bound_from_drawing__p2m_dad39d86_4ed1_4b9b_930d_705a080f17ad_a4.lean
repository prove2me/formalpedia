-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_planar_edge_bound_from_drawing__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- name    : WilliamsonShmoys.component_planar_edge_bound_from_drawing__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T06:09:44.066328+00:00
-- url     : https://prove2.me/theorems/de0e1a5b-8d3a-47e8-9bfe-9457c1edc302
-- title:
--   Planar Euler bound for a connected component
-- statement:
--   A connected component with at least three vertices of a graph with a crossing-free drawing satisfies the simple planar Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.component_planar_edge_bound_from_drawing__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    (hcard : 3 ≤ C.supp.ncard) :
    C.toSimpleGraph.edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by sorry
