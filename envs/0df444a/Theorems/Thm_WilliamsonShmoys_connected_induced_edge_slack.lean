-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_induced_edge_slack
-- name    : WilliamsonShmoys.connected_induced_edge_slack
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:37:24.660769+00:00
-- url     : https://prove2.me/theorems/57f18f9e-054e-4bf4-a81a-9f4063fc028a
-- title:
--   Connected induced piece edge bounds
-- statement:
--   For a connected induced piece, prove the general bound `e(S) ≤ 3|S|−3` and retain the stronger supplied bound whenever `|S| ≥ 3`. For smaller pieces, the general bound follows from the finite simple-graph edge limit.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_induced_edge_slack
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (S : Finset V)
    (hBound : 3 <= S.card -> (L.induce S).Connected ->
      ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6)
    (hConn : (L.induce S).Connected) :
    (((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 3) ∧
      (3 <= S.card -> ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6) := by sorry
