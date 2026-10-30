-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a3
-- name    : WilliamsonShmoys.connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:39.969645+00:00
-- url     : https://prove2.me/theorems/9fc83de8-0852-4661-9f7b-4eaba74d4214
-- title:
--   Connected planar supergraph face count for at least three vertices
-- statement:
--   Given a planar drawing and at least three vertices, the graph is contained in a connected planar supergraph on the same vertices whose edge and face counts satisfy Euler’s relation and the face-incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧
      G.edgeFinset.card ≤ H.edgeSet.ncard ∧
      ∃ f : Nat,
        Fintype.card V + f = H.edgeSet.ncard + 2 ∧
        3 * f ≤ 2 * H.edgeSet.ncard := by sorry
