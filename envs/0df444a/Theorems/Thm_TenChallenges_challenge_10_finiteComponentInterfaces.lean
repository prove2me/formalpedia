-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_finiteComponentInterfaces
-- name    : TenChallenges.challenge_10_finiteComponentInterfaces
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:43:56.477591+00:00
-- url     : https://prove2.me/theorems/3986782a-0f2d-4169-a9e3-7921de1417f8
-- title:
--   Unfriendly partitions for finite component interfaces and locally finite hub sharing (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph and call its infinite-degree vertices hubs. Assume that for each component $C$ of the subgraph induced by the finite-degree vertices there are only finitely many edges between $C$ and the hubs. On the hubs, form a graph $R$ by joining two distinct hubs when infinitely many finite-degree components contain a neighbour of both. Assume $R$ is locally finite.
--
--   Then $G$ has an unfriendly partition, a two-colouring in which each vertex has at least as many opposite-coloured neighbours as same-coloured neighbours. The Partitioner also wins the Challenge 10 game from the empty partition for every ordinal clock.
--
--   The finite-degree components may be infinite. The sharing graph $R$ may also have infinite connected components and triangles.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). Finite-interface extension of the locally finite sharing theorem at https://prove2.me/theorems/a1003729-ae62-4f12-af15-dbbb49a96beb.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u v

namespace TenChallenges
theorem challenge_10_finiteComponentInterfaces {V : Type u} [Countable V] (G : SimpleGraph V)
    (hinterface : ∀ C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent,
      {e : V × V | (G.neighborSet e.1).Infinite ∧ e.2 ∈ Subtype.val '' C.supp ∧ G.Adj e.1 e.2}.Finite)
    (R : SimpleGraph {x : V | (G.neighborSet x).Infinite})
    (hAdj : ∀ x y, R.Adj x y ↔ x ≠ y ∧
      {C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent |
        (∃ a ∈ C.supp, G.Adj x.val a.val) ∧ (∃ b ∈ C.supp, G.Adj y.val b.val)}.Infinite)
    (hloc : ∀ x, (R.neighborSet x).Finite) :
    (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
      ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
