-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_large__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound_large__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:48.589203+00:00
-- url     : https://prove2.me/theorems/f281671c-d623-4140-b8c6-78197a35da85
-- title:
--   Connected planar edge bound for at least three vertices
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_large__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 3 ≤ 3 * Fintype.card V := by sorry
