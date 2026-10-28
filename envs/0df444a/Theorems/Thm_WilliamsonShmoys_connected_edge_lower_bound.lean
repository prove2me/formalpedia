-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound
-- name    : WilliamsonShmoys.connected_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:46:43.655527+00:00
-- url     : https://prove2.me/theorems/953e52e7-54e2-413b-8bd6-7e784b44f554
-- title:
--   Connected finite graphs have at least |V| − 1 edges
-- statement:
--   A finite connected simple graph has at least one fewer edge than vertices. There is no lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 := by sorry
