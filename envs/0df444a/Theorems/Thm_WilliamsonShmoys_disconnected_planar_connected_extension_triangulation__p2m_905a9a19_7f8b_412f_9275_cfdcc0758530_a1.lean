-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_extension_triangulation__p2m_905a9a19_7f8b_412f_9275_cfdcc0758530_a1
-- name    : WilliamsonShmoys.disconnected_planar_connected_extension_triangulation__p2m_905a9a19_7f8b_412f_9275_cfdcc0758530_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:19.606204+00:00
-- url     : https://prove2.me/theorems/f4393a1a-6488-409a-9977-8b12369644ba
-- title:
--   Triangulate a planar graph without adding vertices
-- statement:
--   Every disconnected graph on at least three vertices with the given crossing-free drawing has a connected planar supergraph on the same vertices that contains all its edges and has the edge count of a triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_connected_extension_triangulation__p2m_905a9a19_7f8b_412f_9275_cfdcc0758530_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hdisconn : ¬ N.Connected) :
    ∃ H : SimpleGraph V, N ≤ H ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       N.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
