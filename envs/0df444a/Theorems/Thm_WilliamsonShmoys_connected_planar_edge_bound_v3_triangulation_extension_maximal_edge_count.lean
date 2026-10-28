-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3_triangulation_extension_maximal_edge_count
-- name    : WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:27:28.047847+00:00
-- url     : https://prove2.me/theorems/767a96a1-3258-46ce-b8a9-309c7b787964
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable supergraph on the same vertex type has exactly 3n−6 edges. The boundary n=3 is included; maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
