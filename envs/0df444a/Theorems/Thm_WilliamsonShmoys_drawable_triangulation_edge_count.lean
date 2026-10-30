-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_edge_count
-- name    : WilliamsonShmoys.drawable_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:09:46.109181+00:00
-- url     : https://prove2.me/theorems/5e5b3057-d7a5-459d-a048-d591110d0b0b
-- title:
--   Drawable graphs admit a triangulated edge-maximal extension
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V, G <= U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
