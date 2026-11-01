-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:58:15.914859+00:00
-- url     : https://prove2.me/theorems/41a70d26-a66a-4916-a2c6-308943ffd553
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying the given crossing-free arc conditions has at most 3|V|−6 edges. This isolates the topological core. A proof route handles trees directly; otherwise Euler’s formula for a connected plane graph and the lower bound of three on face boundary lengths give the inequality, accounting for bridges in the face-incidence count. The stated vertex threshold is preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U) (hconn : U.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
