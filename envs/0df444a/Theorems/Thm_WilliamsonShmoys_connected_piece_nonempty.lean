-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_piece_nonempty
-- name    : WilliamsonShmoys.connected_piece_nonempty
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:38:39.981588+00:00
-- url     : https://prove2.me/theorems/dc7ab364-9f8b-45fb-874e-0cafb1cd9474
-- title:
--   A connected induced block is nonempty
-- statement:
--   If the graph induced by a finite set is connected, that set is nonempty. Unfold connectedness and show the empty vertex type cannot satisfy it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_piece_nonempty
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected) :
    0 < S.card := by sorry
