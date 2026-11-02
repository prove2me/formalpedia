-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_extension__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
-- name    : WilliamsonShmoys.connected_planar_maximal_extension__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:56:08.10211+00:00
-- url     : https://prove2.me/theorems/edd1ad18-cf64-45e0-9509-bff7ad919a22
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every connected graph with the stated finite drawing and at least three vertices is a subgraph of an inclusion-maximal drawable simple graph on the same vertices, with its edge count no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_maximal_extension__p2m_f281671c_d623_4140_b8c6_78197a35da85_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
      (letI : DecidableRel G.Adj := dG
       letI : DecidableRel H.Adj := dH
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) := by sorry
