-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:49.849337+00:00
-- url     : https://prove2.me/theorems/b6befa6f-bbd0-4db9-9632-8e3f38d3e7e4
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with at least three vertices and the supplied crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_6fae641e_69bd_437f_8912_51466427af04_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : G.Connected) (hG : HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
