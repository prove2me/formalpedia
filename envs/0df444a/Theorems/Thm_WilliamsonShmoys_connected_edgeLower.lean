-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edgeLower
-- name    : WilliamsonShmoys.connected_edgeLower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:13:54.975372+00:00
-- url     : https://prove2.me/theorems/397b735e-eefa-4287-8750-e554763db207
-- title:
--   Connected graph edge lower bound
-- statement:
--   A connected finite simple graph has at least one fewer edge than vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_edgeLower
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V <= G.edgeSet.ncard + 1 := by sorry
