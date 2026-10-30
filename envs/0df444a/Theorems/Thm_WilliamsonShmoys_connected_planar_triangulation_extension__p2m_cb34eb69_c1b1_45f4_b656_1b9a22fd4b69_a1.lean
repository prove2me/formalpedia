-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_extension__p2m_cb34eb69_c1b1_45f4_b656_1b9a22fd4b69_a1
-- name    : WilliamsonShmoys.connected_planar_triangulation_extension__p2m_cb34eb69_c1b1_45f4_b656_1b9a22fd4b69_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:53:49.320011+00:00
-- url     : https://prove2.me/theorems/e657dedf-589f-4338-b1cf-3cbd004df18d
-- title:
--   Triangulation extension of a connected planar graph
-- statement:
--   Every finite connected simple graph on at least three vertices with a crossing-free drawing extends, on the same vertex set, to a planar simple supergraph with exactly 3n−6 edges. The child makes edge-count monotonicity explicit for the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_triangulation_extension__p2m_cb34eb69_c1b1_45f4_b656_1b9a22fd4b69_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
