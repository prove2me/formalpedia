-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- name    : WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:59.777261+00:00
-- url     : https://prove2.me/theorems/8c5f7fcd-4410-4b31-b397-bfdf744b7888
-- title:
--   Euler edge bound for a connected planar graph
-- statement:
--   For a connected graph with the target’s crossing-free drawing and at least three vertices, prove the Euler edge bound. This isolates face counting from the parent’s disconnected case. A proof route is to form the plane embedding’s faces, use Euler’s relation, count each edge twice in face boundaries, and show each face boundary has length at least three using simplicity and the vertex-count hypothesis. The remaining core obligation is formalizing those face and boundary counts from the given arc-based drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
