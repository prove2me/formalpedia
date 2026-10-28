-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_edge_bound_20261026
-- name    : WilliamsonShmoys.connected_planar_simple_edge_bound_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:30:37.195056+00:00
-- url     : https://prove2.me/theorems/b9c732c7-06bf-4561-9c9a-ce1a69c81dba
-- title:
--   Connected planar simple graph edge bound
-- statement:
--   A connected simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_simple_edge_bound_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
