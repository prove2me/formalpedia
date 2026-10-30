-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_completion_edge_count_of_maximal
-- name    : WilliamsonShmoys.drawable_graph_completion_edge_count_of_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:13:12.863128+00:00
-- url     : https://prove2.me/theorems/f81737ec-3af4-4dcc-9776-b048b7817f27
-- title:
--   A maximal drawable graph has the planar triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable supergraph on the same vertices has exactly 3n − 6 edges. The proof route is to show maximality forces a triangulation and then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_completion_edge_count_of_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
