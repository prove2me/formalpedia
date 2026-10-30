-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
-- name    : WilliamsonShmoys.connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:33.74826+00:00
-- url     : https://prove2.me/theorems/192fbe25-6201-41d9-86bd-b3deef0e6c8e
-- title:
--   Connected planar supergraph face count
-- statement:
--   A finite graph with the given crossing-free drawing is a subgraph of a connected planar graph on the same vertices whose number of faces and edge incidences satisfy Euler’s relation and the face-degree bound. The edge-cardinality comparison transfers the eventual bound to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_supergraph_face_count__p2m_57c3e2f0_3143_4ad3_84d0_92c0d48df09b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧
      G.edgeFinset.card ≤ H.edgeSet.ncard ∧
      ∃ f : Nat,
        Fintype.card V + f = H.edgeSet.ncard + 2 ∧
        3 * f ≤ 2 * H.edgeSet.ncard := by sorry
