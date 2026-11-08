-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_finite
-- name    : TenChallenges.challenge_10_finite
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-04T20:45:25.416798+00:00
-- url     : https://prove2.me/theorems/bd5c6220-4612-4ad0-af7a-4927133dcd62
-- title:
--   Partitioner wins on every finite graph, for every clock
-- statement:
--   **Partitioner wins on every finite graph, for every clock.** For every finite vertex type $V$, every graph $G$ on $V$ and every ordinal $r$, Partitioner has a winning strategy in the $r$-partitioning game on $G$ from the empty partial partition:
--
--   $$\forall G \text{ finite}\ \ \forall r\in\mathrm{Ord}:\quad \mathrm{PartitionerWins}(G,\emptyset,r).$$
-- source:
--   Every finite graph has an unfriendly partition (a partition with the maximum number of crossing edges); e.g. R. Aharoni, E. C. Milner, K. Prikry, Unfriendly partitions of a graph, JCTB 50 (1990), introduction, https://doi.org/10.1016/0095-8956(90)90092-E; game form from the Ten Challenges website, challenge 10

import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace TenChallenges
theorem challenge_10_finite : ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (r : Ordinal.{v}),
    PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
