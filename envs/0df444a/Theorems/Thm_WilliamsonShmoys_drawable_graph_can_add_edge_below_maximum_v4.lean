-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_can_add_edge_below_maximum_v4
-- name    : WilliamsonShmoys.drawable_graph_can_add_edge_below_maximum_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:56:31.256083+00:00
-- url     : https://prove2.me/theorems/f5fc266f-4bfe-4140-8e10-a4c67b5f613a
-- title:
--   A drawable graph below the planar edge bound has a drawable strict extension
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a drawable strict supergraph on the same vertices. At |V| = 3, the strict inequality means an edge is missing from the triangle, and that edge can be added.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_can_add_edge_below_maximum_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hBelow : (L.edgeSet.ncard : Int) <
      3 * (Fintype.card V : Int) - 6) :
    ∃ M : SimpleGraph V, L < M ∧ HasPlanarDrawingOn M := by sorry
