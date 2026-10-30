-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension_for_maximality
-- name    : WilliamsonShmoys.drawable_graph_has_triangulation_extension_for_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:35:33.155697+00:00
-- url     : https://prove2.me/theorems/719c6bb7-9aa0-4725-9f39-6c34f4357440
-- title:
--   Drawable graphs extend to a triangulation
-- statement:
--   A drawable graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulation_extension_for_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
