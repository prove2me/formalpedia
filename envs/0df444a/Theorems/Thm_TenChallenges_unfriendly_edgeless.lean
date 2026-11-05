-- Prove2me | Theorems.Thm_TenChallenges_unfriendly_edgeless
-- name    : TenChallenges.unfriendly_edgeless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:37.048616+00:00
-- url     : https://prove2.me/theorems/b2d7d653-e0f4-49f3-bfc2-faf99f7bc480
-- title:
--   Unfriendly partitions: Edgeless graphs, every ordinal clock
-- statement:
--   On an edgeless graph, every finite partial coloring is a winning position for Partitioner, for every ordinal clock.
-- source:
--   Elementary special case / supporting lemma for Challenge 10. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_TenChallenges_Challenge_10
open scoped Cardinal

theorem TenChallenges.unfriendly_edgeless {V : Type*} (f : V → Option Bool) (hf : HasFiniteDomain f)
    (α : Ordinal) : PartitionerWins (⊥ : SimpleGraph V) f α := by sorry
