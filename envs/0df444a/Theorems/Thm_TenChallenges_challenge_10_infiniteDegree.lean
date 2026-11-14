-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_infiniteDegree
-- name    : TenChallenges.challenge_10_infiniteDegree
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T02:42:48.863408+00:00
-- url     : https://prove2.me/theorems/7f4252c4-0b4b-4741-a6dd-5e63cac137b8
-- title:
--   Challenge 10: all ordinal clocks on graphs with every degree infinite
-- statement:
--   Let $G=(V,E)$ be a simple graph such that every vertex has infinitely many neighbors, and let $f:V\to\{0,1,\bot\}$ be a partial coloring with finite colored domain. For every ordinal $r$, Partitioner has a winning strategy in the unfriendly partition game starting from $f$:
--
--   $$\operatorname{PartitionerWins}(G,f,r).$$
--
--   At each move, Challenger chooses a vertex and a strictly smaller ordinal clock. Partitioner must extend the current finite coloring so that the queried vertex has at least as many opposite-colored neighbors as same-colored neighbors. In particular, the conclusion holds from the empty coloring at every ordinal clock. This proves the infinite-degree-at-every-vertex case of Challenge 10; no countability assumption on $V$ is required.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10; infinite-degree special case using the canonical unfriendly-partition game definitions. https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace TenChallenges
theorem challenge_10_infiniteDegree {V : Type u} (G : SimpleGraph V)
    (hG : ∀ x, (G.neighborSet x).Infinite) (r : Ordinal.{v})
    {f : V → Option Bool} (hf : HasFiniteDomain f) : PartitionerWins G f r := by sorry
end TenChallenges
