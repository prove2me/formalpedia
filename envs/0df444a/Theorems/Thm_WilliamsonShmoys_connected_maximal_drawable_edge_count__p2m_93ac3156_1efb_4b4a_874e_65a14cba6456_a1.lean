-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_edge_count__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- name    : WilliamsonShmoys.connected_maximal_drawable_edge_count__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:40:21.568981+00:00
-- url     : https://prove2.me/theorems/6ce17d90-7e34-4ced-9818-f205b3115d6a
-- title:
--   Edge count of a connected maximal drawable graph
-- statement:
--   A connected drawable graph that is maximal among drawable supergraphs has exactly 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_maximal_drawable_edge_count__p2m_93ac3156_1efb_4b4a_874e_65a14cba6456_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : P.Connected) (hP : HasPlanarDrawingOn P) (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) : P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
