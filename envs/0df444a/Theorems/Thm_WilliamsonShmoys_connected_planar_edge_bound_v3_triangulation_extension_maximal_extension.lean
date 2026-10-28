-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3_triangulation_extension_maximal_extension
-- name    : WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:21:31.555966+00:00
-- url     : https://prove2.me/theorems/42662890-9024-415e-8301-92f65dfcad8c
-- title:
--   Maximal drawable extension on the same vertices
-- statement:
--   Extend the given connected drawable graph to an inclusion-maximal drawable graph on the same finite ordered vertex type, retaining every original edge. The edge count is monotone under this extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
