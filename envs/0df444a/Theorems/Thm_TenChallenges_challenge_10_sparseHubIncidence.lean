-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_sparseHubIncidence
-- name    : TenChallenges.challenge_10_sparseHubIncidence
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T07:17:12.546111+00:00
-- url     : https://prove2.me/theorems/3d33b371-b711-48e7-89d3-7c3f937d0511
-- title:
--   All ordinal clocks with sparse incidence to infinite-degree vertices (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph. Suppose each finite-degree vertex has at most one infinite-degree neighbour, or has even degree and at most two infinite-degree neighbours. Then Partitioner wins the Challenge 10 game from the empty partial partition for every ordinal clock. Edges between infinite-degree vertices are unrestricted.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). This theorem proves the all-clock conclusion for graphs satisfying the stated incidence condition.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Data.Set.Card
universe u v

namespace TenChallenges
theorem challenge_10_sparseHubIncidence {V : Type u} [Countable V] (G : SimpleGraph V)
    (hthin : ∀ x, (G.neighborSet x).Finite →
      (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).ncard ≤ 1 ∨
        (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).ncard ≤ 2 ∧
          Even (G.neighborSet x).ncard) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
