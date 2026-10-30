-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedPlanar_edgeBound
-- name    : WilliamsonShmoys.connectedPlanar_edgeBound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:55:34.955989+00:00
-- url     : https://prove2.me/theorems/5b303e28-bf40-4827-ac04-6d36d7c50248
-- title:
--   Edge bound for connected finite simple planar graphs
-- statement:
--   A connected finite simple graph on at least three vertices with the given crossing-free drawing has at most three times its number of vertices minus six edges. This is the Euler-formula core: count edge-sides on face boundaries and combine that count with the lower bound on face-boundary lengths for a simple graph with at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connectedPlanar_edgeBound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
