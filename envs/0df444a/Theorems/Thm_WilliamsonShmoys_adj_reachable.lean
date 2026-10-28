-- Prove2me | Theorems.Thm_WilliamsonShmoys_adj_reachable
-- name    : WilliamsonShmoys.adj_reachable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:44:54.038984+00:00
-- url     : https://prove2.me/theorems/3edd4740-d325-44c2-a903-e243e677f839
-- title:
--   An adjacent pair is reachable
-- statement:
--   For a simple graph, an edge between two vertices gives a walk connecting them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.adj_reachable
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : G.Reachable u v := by
  sorry
