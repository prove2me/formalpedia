-- Prove2me | Theorems.Thm_TenChallenges_unfriendly_partition_iff_all_clocks
-- name    : TenChallenges.unfriendly_partition_iff_all_clocks
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T03:21:02.163604+00:00
-- url     : https://prove2.me/theorems/a5f24355-a147-4535-8268-9ea859c12957
-- title:
--   Challenge 10: global unfriendly partitions iff every ordinal clock is winning
-- statement:
--   Let $G=(V,E)$ be a countable simple graph. A two-coloring is unfriendly if each vertex has at least as many neighbors of the opposite color as of its own color. Then
--
--   $$G\text{ admits a global unfriendly partition}\quad\Longleftrightarrow\quad\forall\alpha\in\mathrm{Ord},\ \text{Partitioner wins the }\alpha\text{-partitioning game on }G.$$
--
--   In the game, Challenger chooses a vertex and a strictly smaller ordinal clock; Partitioner responds with a finite extension of the current partial coloring that is unfriendly at the queried vertex. This equivalence relates the global existence question to the complete family of scaled games. It does not assert that either condition holds for every countable graph.
--
--   Formalization note: if $V:\mathrm{Type}\,u$, the clock quantifier ranges over $\mathrm{Ordinal}.\{u\}$. The formal coloring has type $V\to\mathrm{Option}(\mathrm{Bool})$; unfriendliness at every vertex requires the coloring to be total.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10; equivalence between the global unfriendly partition assertion and its full family of ordinal-clock games, using canonical definitions. https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_10
universe u

namespace TenChallenges
theorem unfriendly_partition_iff_all_clocks {V : Type u} [Countable V]
    (G : SimpleGraph V) :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ↔
      ∀ α : Ordinal.{u}, PartitionerWins G (emptyPartition V) α := by sorry
end TenChallenges
