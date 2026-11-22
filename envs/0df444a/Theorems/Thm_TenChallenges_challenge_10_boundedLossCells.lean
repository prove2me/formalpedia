-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_boundedLossCells
-- name    : TenChallenges.challenge_10_boundedLossCells
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T07:56:32.805105+00:00
-- url     : https://prove2.me/theorems/1418ee16-e5c4-4156-a130-bb241c57349b
-- title:
--   Unfriendly partitions and all ordinal clocks for cells with finite interfaces (Challenge 10)
-- statement:
--   Let the vertices of a countable simple graph be partitioned into cells. Each cell contains finitely many infinite-degree vertices, and each such vertex has infinitely many finite-degree neighbours in its own cell. For each cell, only finitely many edges join a finite-degree vertex of that cell to a vertex outside it. Then the graph has an unfriendly two-colouring, and Partitioner wins the Challenge 10 game from the empty partial partition for every ordinal clock. Cells may be infinite, and there is no common bound on their interfaces.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). Supplementary theorem for the stated class of graphs.

import Definitions.Def_TenChallenges_Challenge_10
universe u w v

namespace TenChallenges
theorem challenge_10_boundedLossCells {V : Type u} {ι : Type w} [Countable V]
    (G : SimpleGraph V) (owner : V → ι)
    (hH : ∀ i, {x : V | (G.neighborSet x).Infinite ∧ owner x = i}.Finite)
    (hN : ∀ i h, (G.neighborSet h).Infinite ∧ owner h = i →
      (G.neighborSet h ∩ {x : V | (G.neighborSet x).Finite ∧ owner x = i}).Infinite)
    (hI : ∀ i, {e : V × V | G.Adj e.1 e.2 ∧
      (((G.neighborSet e.1).Finite ∧ owner e.1 = i) ∧ owner e.2 ≠ i ∨
       ((G.neighborSet e.2).Finite ∧ owner e.2 = i) ∧ owner e.1 ≠ i)}.Finite) :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ∧
      ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
