-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_extension_20261026
-- name    : WilliamsonShmoys.connected_planar_drawing_triangulation_extension_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:44:47.725798+00:00
-- url     : https://prove2.me/theorems/3d981a85-892d-475c-a119-215e59aba634
-- title:
--   Triangulation extension of a connected planar drawing
-- statement:
--   Any connected simple graph on at least three vertices with the supplied crossing-free drawing can be extended, without adding vertices, to a simple graph with a crossing-free drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_triangulation_extension_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
