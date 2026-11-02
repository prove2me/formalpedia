-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
-- name    : WilliamsonShmoys.connected_planar_euler_face_count__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:28.908218+00:00
-- url     : https://prove2.me/theorems/ebc06475-0f55-4f76-ba4b-759451993d0a
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.connected_planar_euler_face_count__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     ∃ f : ℕ, Fintype.card V + f = N.edgeFinset.card + 2) := by sorry
