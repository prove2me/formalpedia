-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:57.468738+00:00
-- url     : https://prove2.me/theorems/af58f30d-9690-4bf2-bfba-5c068b1bd46b
-- title:
--   Euler edge bound for a connected drawable graph
-- statement:
--   A connected drawable finite simple graph with at least three vertices satisfies the Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hConnected : G.Connected) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
