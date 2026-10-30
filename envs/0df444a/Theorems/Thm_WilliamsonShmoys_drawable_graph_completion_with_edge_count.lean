-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_completion_with_edge_count
-- name    : WilliamsonShmoys.drawable_graph_completion_with_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:30:14.890069+00:00
-- url     : https://prove2.me/theorems/8b2c3898-2e1e-4e7e-b74c-e70c65707dcf
-- title:
--   A drawable graph has a drawable triangulation completion
-- statement:
--   Every drawable simple graph on a fixed finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_completion_with_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
