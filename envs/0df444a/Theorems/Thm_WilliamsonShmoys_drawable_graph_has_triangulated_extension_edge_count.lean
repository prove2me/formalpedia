-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension_edge_count
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_extension_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:06:26.465114+00:00
-- url     : https://prove2.me/theorems/5e5aee54-9e86-4f67-bd4f-06e7eb077b62
-- title:
--   Triangulated edge-count extension of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices whose edge count is three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulated_extension_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hZdraw : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
