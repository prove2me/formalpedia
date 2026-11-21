-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_triangleFreeSharing
-- name    : TenChallenges.challenge_10_triangleFreeSharing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:10:33.698506+00:00
-- url     : https://prove2.me/theorems/6773d63f-134d-43c3-a87e-61f739d19f6c
-- title:
--   Unfriendly partitions for locally finite triangle-free sharing between hubs (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph and call its infinite-degree vertices hubs. Suppose every component of the subgraph induced by the finite-degree vertices is finite. Form a graph $R$ on the hubs by joining two distinct hubs when infinitely many of those components have a neighbour of each hub. Suppose $R$ is locally finite and triangle-free.
--
--   Then $G$ has an unfriendly partition, a two-colouring in which each vertex has at least as many opposite-coloured neighbours as same-coloured neighbours. The Partitioner also wins the Challenge 10 game from the empty partition for every ordinal clock.
--
--   The graph $R$ may have infinite connected components, such as an infinite path.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). The related finite-block theorem is at https://prove2.me/theorems/ecc12316-1399-41c8-92ee-cbb135dfebb0.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u v

namespace TenChallenges
theorem challenge_10_triangleFreeSharing {V : Type u} [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent, C.supp.Finite)
    (R : SimpleGraph {x : V | (G.neighborSet x).Infinite})
    (hAdj : ∀ x y, R.Adj x y ↔ x ≠ y ∧
      {C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent |
        (∃ a ∈ C.supp, G.Adj x.val a.val) ∧ (∃ b ∈ C.supp, G.Adj y.val b.val)}.Infinite)
    (hloc : ∀ x, (R.neighborSet x).Finite)
    (htriangle : ∀ x y z, R.Adj x y → R.Adj y z → ¬ R.Adj x z) :
    (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
      ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
