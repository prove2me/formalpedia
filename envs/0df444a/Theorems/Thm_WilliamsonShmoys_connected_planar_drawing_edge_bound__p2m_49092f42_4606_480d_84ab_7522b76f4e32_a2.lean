-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:21:32.914874+00:00
-- url     : https://prove2.me/theorems/18a26d28-265e-4bc7-9ca3-5f0740a0d126
-- title:
--   Connected crossing-free drawing edge bound
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hconn : X.Connected) (hV : 3 ≤ Fintype.card V) : X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
