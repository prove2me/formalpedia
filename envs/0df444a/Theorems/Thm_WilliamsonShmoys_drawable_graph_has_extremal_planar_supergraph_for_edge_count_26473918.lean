-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_extremal_planar_supergraph_for_edge_count_26473918
-- name    : WilliamsonShmoys.drawable_graph_has_extremal_planar_supergraph_for_edge_count_26473918
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:44:20.691989+00:00
-- url     : https://prove2.me/theorems/ccb0affb-1193-4385-865c-3b2cb0b9cbb1
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has an inclusion-maximal drawable supergraph on the same vertices. Finiteness of the simple graphs on the vertex type permits maximizing edge count; deleting edges preserves the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_extremal_planar_supergraph_for_edge_count_26473918
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by sorry
