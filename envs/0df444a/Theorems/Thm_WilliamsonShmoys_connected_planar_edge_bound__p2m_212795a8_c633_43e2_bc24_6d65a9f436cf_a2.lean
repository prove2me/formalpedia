-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:12:58.10734+00:00
-- url     : https://prove2.me/theorems/a9372b74-2333-4a1d-b694-ab95253c7875
-- title:
--   Euler edge bound for a connected drawable graph
-- statement:
--   A connected drawable finite simple graph with at least three vertices satisfies the planar edge bound. This isolates the Euler-counting step after the first child handles disconnected graphs. A proof route is to extend the connected drawing to a triangulation on the same vertices, apply Euler’s formula, and count at least three edge-sides per face. The remaining work is formalizing that extension and incidence count for `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
