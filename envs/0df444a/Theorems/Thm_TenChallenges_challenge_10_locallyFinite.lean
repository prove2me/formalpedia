-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_locallyFinite
-- name    : TenChallenges.challenge_10_locallyFinite
-- status  : Proved
-- author  : @utkuokur
-- created : 2026-11-04T20:45:41.560199+00:00
-- url     : https://prove2.me/theorems/36ae2569-22f1-435b-a74b-558ccd5bca49
-- title:
--   Partitioner wins on every countable locally finite graph, for every clock
-- statement:
--   **Partitioner wins on every countable locally finite graph, for every clock.** For every countable vertex type $V$ and every graph $G$ on $V$ in which every vertex has only finitely many neighbours, and every ordinal $r$, Partitioner has a winning strategy in the $r$-partitioning game on $G$ from the empty partial partition:
--
--   $$\forall G \text{ countable, locally finite}\ \ \forall r\in\mathrm{Ord}:\quad \mathrm{PartitionerWins}(G,\emptyset,r).$$
-- source:
--   Locally finite graphs have unfriendly partitions, by compactness from the finite case; R. Aharoni, E. C. Milner, K. Prikry, Unfriendly partitions of a graph, JCTB 50 (1990), https://doi.org/10.1016/0095-8956(90)90092-E, Section 1

import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace TenChallenges
theorem challenge_10_locallyFinite : ∀ {V : Type u} [Countable V] (G : SimpleGraph V),
    (∀ v, (G.neighborSet v).Finite) → ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
