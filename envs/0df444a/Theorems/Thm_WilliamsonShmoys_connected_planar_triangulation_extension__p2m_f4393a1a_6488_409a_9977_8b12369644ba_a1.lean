-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
-- name    : WilliamsonShmoys.connected_planar_triangulation_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:24.530735+00:00
-- url     : https://prove2.me/theorems/06bdf4fe-cd1d-4093-b45f-6118505c9d7e
-- title:
--   Extend a connected planar drawing to a triangulation
-- statement:
--   Every connected planar drawing on at least three vertices extends, without adding vertices, to a connected planar graph with 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_triangulation_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hKconn : K.Connected)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
