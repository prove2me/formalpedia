-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_edge_extension__p2m_aa360b7d_83e7_4a10_9952_960bd13962a8_a1
-- name    : WilliamsonShmoys.disconnected_planar_drawing_edge_extension__p2m_aa360b7d_83e7_4a10_9952_960bd13962a8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:17.685185+00:00
-- url     : https://prove2.me/theorems/d5850897-bb19-4a14-84a1-2d0f5ebfaf1b
-- title:
--   Extend a disconnected planar drawing by an edge
-- statement:
--   Any disconnected graph on a finite linearly ordered vertex type with at least three vertices that has a crossing-free drawing can be extended to a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_drawing_edge_extension__p2m_aa360b7d_83e7_4a10_9952_960bd13962a8_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hDisc : ¬ L.Connected) : ∃ N : SimpleGraph V, L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ ¬ N ≤ L := by sorry
