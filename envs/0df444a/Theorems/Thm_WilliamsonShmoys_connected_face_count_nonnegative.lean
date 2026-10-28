-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_face_count_nonnegative
-- name    : WilliamsonShmoys.connected_face_count_nonnegative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:19:39.377725+00:00
-- url     : https://prove2.me/theorems/d9880edb-f97c-4314-8741-d5ff302dd5d4
-- title:
--   Edge lower bound for a finite connected graph
-- statement:
--   A finite connected graph has at least one fewer edge than vertices. This ensures the target's Euler witness is a natural number without truncation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_face_count_nonnegative
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V <= G.edgeSet.ncard + 1 := by sorry
