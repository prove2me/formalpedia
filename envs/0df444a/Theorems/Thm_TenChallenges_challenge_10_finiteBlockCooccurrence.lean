-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_finiteBlockCooccurrence
-- name    : TenChallenges.challenge_10_finiteBlockCooccurrence
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-20T21:59:24.921533+00:00
-- url     : https://prove2.me/theorems/ecc12316-1399-41c8-92ee-cbb135dfebb0
-- title:
--   Unfriendly partitions for finite blocks of hubs with finite co-occurrence between blocks (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph. Call its infinite-degree vertices hubs and let $\mathcal C$ be the set of connected components of the subgraph induced by its finite-degree vertices. Suppose every $C\in \mathcal C$ is finite. Partition the hubs into finite blocks and suppose that any two hubs $x,y$ in different blocks each have a neighbour in the same component for only finitely many $C\in\mathcal C$.
--
--   Then $G$ has an unfriendly partition, a two-colouring in which each vertex has at least as many opposite-coloured neighbours as same-coloured neighbours. The Partitioner also wins the Challenge 10 game from the empty partition for every ordinal clock.
--
--   The blocks may have unbounded finite sizes. Hubs in the same block may share infinitely many components, and the hypothesis allows infinitely many such blocks.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). Related verified result using a finite exceptional set of hubs: https://prove2.me/theorems/bde24505-29ba-4fa0-bee6-98a2057d3d99.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u v w

namespace TenChallenges
theorem challenge_10_finiteBlockCooccurrence {V : Type u} {I : Type v}
    [Countable V] [Countable I] (G : SimpleGraph V)
    (hfinite : ∀ C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent, C.supp.Finite)
    (block : {h : V | (G.neighborSet h).Infinite} → I)
    (hblocks : ∀ i : I, {h : {h : V | (G.neighborSet h).Infinite} | block h = i}.Finite)
    (hshare : ∀ x y : {h : V | (G.neighborSet h).Infinite}, block x ≠ block y →
      {C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent |
        (∃ a ∈ C.supp, G.Adj x.val a.val) ∧ (∃ b ∈ C.supp, G.Adj y.val b.val)}.Finite) :
    (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
      ∀ r : Ordinal.{w}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
