-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
-- name    : WilliamsonShmoys.connected_planar_edge_bound_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:59:43.536616+00:00
-- url     : https://prove2.me/theorems/8a575182-b8ab-492a-b851-6ab39c9a2ece
-- title:
--   Euler edge bound for a connected planar graph
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. The proof obligation is to formalize the Euler face-count argument for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_edge_bound_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
