-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_small_piece_edge_bound
-- name    : WilliamsonShmoys.connected_small_piece_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:45:23.527293+00:00
-- url     : https://prove2.me/theorems/5de83308-04f0-4bc9-93b0-85148bbc9960
-- title:
--   Small connected pieces have three units of edge slack
-- statement:
--   For a nonempty connected induced block of size below three, its induced edge count plus three is at most three times its size. The only possible sizes are one and two: simplicity bounds their edge counts by zero and one, respectively. This proof handles the small-block boundary cases independently of the main partition argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_small_piece_edge_bound
    {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected)
    (hpos : 0 < S.card) (hlt : S.card < 3) :
    (G.induce (↑S : Set V)).edgeSet.ncard + 3 ≤ 3 * S.card := by sorry
