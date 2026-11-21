-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_locallyFiniteSharing
-- name    : TenChallenges.challenge_10_locallyFiniteSharing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:37:23.821098+00:00
-- url     : https://prove2.me/theorems/a1003729-ae62-4f12-af15-dbbb49a96beb
-- title:
--   Unfriendly partitions for locally finite recurrent sharing between hubs (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph and call its infinite-degree vertices hubs. Suppose every component of the subgraph induced by the finite-degree vertices is finite. Form a graph $R$ on the hubs by joining two distinct hubs when infinitely many of those components contain a neighbour of each hub. Assume that each vertex of $R$ has finite degree.
--
--   Then $G$ has an unfriendly partition, a two-colouring in which each vertex has at least as many opposite-coloured neighbours as same-coloured neighbours. The Partitioner also wins the Challenge 10 game from the empty partition for every ordinal clock.
--
--   The sharing graph $R$ can have infinite connected components, triangles and vertices of unbounded finite degree.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). This extends the triangle-free sharing result at https://prove2.me/theorems/6773d63f-134d-43c3-a87e-61f739d19f6c.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u v

namespace TenChallenges
theorem challenge_10_locallyFiniteSharing {V : Type u} [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent, C.supp.Finite)
    (R : SimpleGraph {x : V | (G.neighborSet x).Infinite})
    (hAdj : ∀ x y, R.Adj x y ↔ x ≠ y ∧
      {C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent |
        (∃ a ∈ C.supp, G.Adj x.val a.val) ∧ (∃ b ∈ C.supp, G.Adj y.val b.val)}.Infinite)
    (hloc : ∀ x, (R.neighborSet x).Finite) :
    (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
      ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
