-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_extension__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
-- name    : WilliamsonShmoys.disconnected_planar_connected_extension__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:05.713579+00:00
-- url     : https://prove2.me/theorems/905a9a19-7f8b-412f-9275-cfdcc0758530
-- title:
--   Connect a disconnected planar drawing by adding edges
-- statement:
--   Extend a disconnected drawable graph to a connected drawable supergraph on the same vertices, with no decrease in edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_connected_extension__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hdisconn : ¬ N.Connected) :
    ∃ H : SimpleGraph V, N ≤ H ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       N.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
