-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_finiteKernelCooccurrence
-- name    : TenChallenges.challenge_10_finiteKernelCooccurrence
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-20T21:33:37.347106+00:00
-- url     : https://prove2.me/theorems/bde24505-29ba-4fa0-bee6-98a2057d3d99
-- title:
--   Unfriendly partitions when a finite set meets every pair of hubs sharing infinitely many components (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph, let $I$ be its set of infinite-degree vertices (the hubs), and let $\mathcal C$ be the components of the subgraph induced by the finite-degree vertices. Let $\partial C$ consist of the hubs with a neighbour in $C$. Suppose each $C\in\mathcal C$ is finite and there is a finite set $K$ of vertices such that
--
--   $$\bigl|\{C\in\mathcal C : x,y\in\partial C\}\bigr|<\aleph_0
--   \qquad\text{for distinct }x,y\in I\setminus K.$$
--
--   Then $G$ has an unfriendly partition. In this two-colouring, each vertex has at least as many neighbours of the opposite colour as of its own colour. The Partitioner also wins the Challenge 10 game from the empty partition for every ordinal clock.
--
--   For example, $K$ can consist of two hubs. Either of them can share infinitely many components with the other and with any number of further hubs. The hypotheses allow unbounded component sizes and unbounded numbers of hubs on their boundaries.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). The empty exceptional set gives the previously verified finite co-occurrence theorem (https://prove2.me/theorems/d46ffd21-6325-43b6-9328-8dbab61536ae).

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u v

namespace TenChallenges
theorem challenge_10_finiteKernelCooccurrence {V : Type u} [Countable V] (G : SimpleGraph V)
    (K : Set V) (hK : K.Finite)
    (hfinite : ∀ C : (G.induce {v : V | (G.neighborSet v).Finite}).ConnectedComponent, C.supp.Finite)
    (hshare : ∀ x y : V, x ∉ K → y ∉ K → (G.neighborSet x).Infinite →
      (G.neighborSet y).Infinite → x ≠ y →
        {C : (G.induce {v : V | (G.neighborSet v).Finite}).ConnectedComponent |
          (∃ a ∈ C.supp, G.Adj x a.val) ∧ (∃ b ∈ C.supp, G.Adj y b.val)}.Finite) :
    (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
      ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
