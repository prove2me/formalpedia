-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_overlappingComponentInterfaces
-- name    : TenChallenges.challenge_10_overlappingComponentInterfaces
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T05:05:24.067401+00:00
-- url     : https://prove2.me/theorems/62dab995-409c-4d96-a841-9a1ed20aab52
-- title:
--   Unfriendly partitions with overlapping infinite component interfaces (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph. Write $H$ for its infinite-degree vertices (the hubs) and let $\mathcal C$ be the components induced by the finite-degree vertices. For each $C\in\mathcal C$, put
--   $$
--   D_C=\{x\in H : x\text{ has infinitely many neighbours in }C\},
--   \qquad U=\bigcup_{C\in\mathcal C}D_C.
--   $$
--   Assume each $D_C$ is finite and only finitely many edges join $C$ to $H\setminus D_C$. On $H\setminus U$, form a graph $R$ by joining distinct hubs when infinitely many $C\in\mathcal C$ contain a neighbour of both. Assume $R$ is locally finite.
--
--   Then $G$ has an unfriendly partition, a two-colouring in which each vertex has at least as many opposite-coloured neighbours as same-coloured neighbours. The Partitioner also wins the Challenge 10 game from the empty partition for every ordinal clock.
--
--   The sets $D_C$ may overlap, and the finite-degree components may be infinite.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). This extends the finite-interface theorem at https://prove2.me/theorems/3986782a-0f2d-4169-a9e3-7921de1417f8.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u v

namespace TenChallenges
theorem challenge_10_overlappingComponentInterfaces {V : Type u} [Countable V] (G : SimpleGraph V) :
    let H : Set V := {v | (G.neighborSet v).Infinite}
    let Comp := (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent
    let A (C : Comp) : Set V := Subtype.val '' C.supp
    let demand (C : Comp) : Set V := {x | x ∈ H ∧ (G.neighborSet x ∩ A C).Infinite}
    let U : Set V := ⋃ C, demand C
    ∀ (hDemand : ∀ C : Comp, (demand C).Finite)
      (hEdges : ∀ C : Comp, {e : V × V |
        e.1 ∈ H \ demand C ∧ e.2 ∈ A C ∧ G.Adj e.1 e.2}.Finite)
      (R : SimpleGraph ↑(H \ U))
      (hAdj : ∀ x y, R.Adj x y ↔ x ≠ y ∧
        {C : Comp |
          (∃ a ∈ C.supp, G.Adj x.val a.val) ∧ (∃ b ∈ C.supp, G.Adj y.val b.val)}.Infinite)
      (hloc : ∀ x, (R.neighborSet x).Finite),
      (∃ f : V → Option Bool, ∀ x : V, UnfriendlyAt G f x) ∧
        ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by sorry
end TenChallenges
