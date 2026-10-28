-- Prove2me | Theorems.Thm_WilliamsonShmoys_aggregate_connected_piece_slack
-- name    : WilliamsonShmoys.aggregate_connected_piece_slack
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:42:55.668354+00:00
-- url     : https://prove2.me/theorems/d14d59b9-c337-4396-ada5-9993c9ba2f09
-- title:
--   Aggregate piece edge slack
-- statement:
--   Aggregate the per-piece bounds using the piece-size sum and edge-count equality. A singleton family uses its piece’s stronger bound; a family with at least two members sums the weaker bounds and obtains at least six units of total slack.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.aggregate_connected_piece_slack
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (C : Finset (Finset V))
    (hCard : 3 <= Fintype.card V)
    (hCardSum : ∑ S ∈ C, S.card = Fintype.card V)
    (hEdgeSum : (L.edgeSet.ncard : Int) =
      ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int))
    (hPiece : ∀ S ∈ C,
      (((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 3) ∧
        (3 <= S.card -> ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6)) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
