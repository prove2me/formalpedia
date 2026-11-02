-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:27.993991+00:00
-- url     : https://prove2.me/theorems/2921e68e-aa42-4dea-8127-751b3e371ec8
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   Every finite connected simple graph with a crossing-free drawing satisfies the planar edge bound in the form `edge count + 3 ≤ 3 * vertex count`. For at least three vertices this follows from Euler’s formula and the minimum face-boundary length; the one- and two-vertex cases follow directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 3 ≤ 3 * Fintype.card V := by sorry
