-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1
-- name    : WilliamsonShmoys.connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:15:45.540994+00:00
-- url     : https://prove2.me/theorems/189aab1a-280b-4ab3-961b-1c0b2454cb23
-- title:
--   Euler and face-boundary certificate for a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a finite face count satisfying Euler’s equation and the lower bound on total face-boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_count_certificate__p2m_0a6cb8c8_85f4_4527_b550_0c59830e1a8e_a1 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ f : ℕ, f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
