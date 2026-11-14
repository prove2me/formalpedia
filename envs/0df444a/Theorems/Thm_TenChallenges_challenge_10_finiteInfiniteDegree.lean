-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_finiteInfiniteDegree
-- name    : TenChallenges.challenge_10_finiteInfiniteDegree
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T04:39:09.950021+00:00
-- url     : https://prove2.me/theorems/2131d288-a2ea-49ab-bd2f-c94dad2afa9f
-- title:
--   Challenge 10: every ordinal clock with finitely many infinite-degree vertices
-- statement:
--   Let $G=(V,E)$ be a countable simple graph such that only finitely many vertices have infinite degree. Then Partitioner wins the unfriendly partitioning game from the empty partial coloring for every ordinal clock:
--
--   $$\forall\alpha\in\mathrm{Ord},\quad \operatorname{PartitionerWins}(G,\varnothing,\alpha).$$
--
--   At each turn, Challenger chooses a vertex and a strictly smaller ordinal clock. Partitioner supplies a finite extension of the current partial coloring that makes the queried vertex have at least as many colored neighbors of the opposite color as of its own color.
--
--   This is the ordinal-game consequence of the Aharoni–Milner–Prikry theorem that graphs with finitely many infinite-degree vertices admit an unfriendly partition. It includes the locally finite case and allows arbitrary interaction between finite-degree vertices and the finitely many infinite-degree vertices.
--
--   Formalization note: the vertex and clock universes are independent. The statement concerns the canonical `PartitionerWins` and `emptyPartition` definitions. It does not cover graphs with infinitely many infinite-degree vertices.
-- source:
--   R. Aharoni, E. C. Milner, K. Prikry, Unfriendly partitions of a graph, Journal of Combinatorial Theory Series B 50 (1990), 1–10, Theorem 1, https://doi.org/10.1016/0095-8956(90)90092-E; finite-repair formulation in L. Aurichi and L. Real, Remarks on the countable case of the Unfriendly Partition Problem, Lemma 2.1, https://arxiv.org/abs/2412.14151; ordinal-game consequence for Ten Challenges, Challenge 10, https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace TenChallenges
theorem challenge_10_finiteInfiniteDegree {V : Type u} [Countable V]
    (G : SimpleGraph V)
    (hI : {x : V | (G.neighborSet x).Infinite}.Finite)
    (r : Ordinal.{v}) : PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
