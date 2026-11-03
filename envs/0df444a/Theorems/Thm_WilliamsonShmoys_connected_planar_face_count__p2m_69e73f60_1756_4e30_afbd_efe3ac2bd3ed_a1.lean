-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_count__p2m_69e73f60_1756_4e30_afbd_efe3ac2bd3ed_a1
-- name    : WilliamsonShmoys.connected_planar_face_count__p2m_69e73f60_1756_4e30_afbd_efe3ac2bd3ed_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:50.353653+00:00
-- url     : https://prove2.me/theorems/7e43e1d3-8cc5-4078-adc3-512d6b4c19e6
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s formula and the lower bound of three edge incidences per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_face_count__p2m_69e73f60_1756_4e30_afbd_efe3ac2bd3ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     ∃ f : ℕ,
       Fintype.card V + f = N.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * N.edgeFinset.card) := by sorry
