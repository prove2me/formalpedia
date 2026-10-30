-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_extension
-- name    : WilliamsonShmoys.connected_planar_drawing_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:53:41.270678+00:00
-- url     : https://prove2.me/theorems/ba9c4b13-1fd7-4e21-a515-03aeff8cfe51
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Every connected graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertices whose edge count is exactly three times the vertex count minus six, and whose edge count bounds the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
