-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:41.193685+00:00
-- url     : https://prove2.me/theorems/93e8e51b-b659-4e57-adae-24ec3eefdfaa
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   Every connected drawable simple graph with at least three vertices has at most three times its number of vertices minus six edges. This isolates the Euler counting step; it can be proved from Euler’s formula and the lower bound of three on face-boundary length, counting bridge incidences with multiplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
