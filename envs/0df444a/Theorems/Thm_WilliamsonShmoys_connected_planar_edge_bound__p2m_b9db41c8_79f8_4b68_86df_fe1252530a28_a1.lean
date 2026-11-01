-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:48.570208+00:00
-- url     : https://prove2.me/theorems/792d8105-156d-4ec7-b9fb-1feb01e02200
-- title:
--   Euler edge bound for connected simple planar drawings
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. This isolates the Euler-formula argument from component joining. A proof route is to obtain the plane embedding’s Euler relation, count edge incidences around face boundaries (including repeated incidences at bridges), and use simplicity and n ≥ 3 to get the required face-boundary lower bound; the remaining arithmetic yields 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
