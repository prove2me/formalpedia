-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:09:58.288774+00:00
-- url     : https://prove2.me/theorems/7dadb7da-8b1f-4740-8afa-ded5b834878b
-- title:
--   Face count and boundary incidences from a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing admits a face count satisfying Euler's equation, with total boundary incidences equal to twice the edge count and at least three incidences per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hConn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ F B : Nat, Fintype.card V + F = G.edgeSet.ncard + 2 ∧ B = 2 * G.edgeSet.ncard ∧ 3 * F ≤ B := by sorry
