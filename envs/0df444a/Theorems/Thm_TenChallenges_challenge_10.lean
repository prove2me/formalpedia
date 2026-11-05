-- Prove2me | Theorems.Thm_TenChallenges_challenge_10
-- name    : TenChallenges.challenge_10
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T20:19:31.045455+00:00
-- url     : https://prove2.me/theorems/74b33855-6b35-41b6-8aac-3e35178e4c9e
-- title:
--   Partitioner wins the $r$-partitioning game on every countable graph, for every ordinal $r$
-- statement:
--   **The scaled unfriendly partition conjecture.** For every ordinal $r$ and every graph $G$ on a countable vertex set, Partitioner has a winning strategy in the $r$-partitioning game on $G$: starting from the empty partial partition with clock $r$, whenever Challenger names a vertex $v$ and an ordinal $\beta$ below the current clock, Partitioner can extend the current finite partial partition to a finite partial partition that is unfriendly at $v$, and continue to do so with clock $\beta$:
--
--   $$\forall r\in\mathrm{Ord}\ \ \forall G \text{ countable}:\quad \mathrm{PartitionerWins}(G,\emptyset,r).$$
--
--   An unfriendly partition of $G$ yields such a strategy for every $r$, so the statement follows from the unfriendly partition conjecture for countable graphs. The statement is open for infinite clocks.
--
--   **Formalization Note.** The statement is `∀ r : Ordinal.{v}, statement_10.{u, v} r`, with independent universes for the vertex type and the ordinal.
-- source:
--   Unfriendly partition conjecture (Cowan and Emerson), as stated in R. Aharoni, E. C. Milner, K. Prikry, Unfriendly partitions of a graph, JCTB 50 (1990), https://doi.org/10.1016/0095-8956(90)90092-E; game form in V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 10

import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace TenChallenges
theorem challenge_10 : ∀ r : Ordinal.{v}, statement_10.{u, v} r := by sorry
end TenChallenges
