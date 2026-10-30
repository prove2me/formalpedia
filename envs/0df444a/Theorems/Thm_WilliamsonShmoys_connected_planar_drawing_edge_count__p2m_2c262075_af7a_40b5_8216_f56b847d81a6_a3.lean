-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:06:21.825664+00:00
-- url     : https://prove2.me/theorems/1027980a-6905-43b3-89bc-6a03a3495b4b
-- title:
--   Edge bound for a connected finite simple planar drawing
-- statement:
--   A connected finite simple graph on at least three vertices with the supplied crossing-free drawing has at most `3n−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hConn : T.Connected) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
