-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_stableComponentExtension
-- name    : TenChallenges.challenge_10_stableComponentExtension
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-20T21:00:02.239645+00:00
-- url     : https://prove2.me/theorems/41ac073b-1a74-4299-842a-10fcac5f87b2
-- title:
--   Extending prescribed hub colours to an unfriendly partition (Challenge 10)
-- statement:
--   Let $G$ be a countable simple graph, let $I$ be its infinite-degree vertices (the hubs), and fix a two-colouring $q$ of the hubs. Suppose every component of the subgraph obtained by deleting $I$ is finite. A colouring is *unfriendly* at a vertex if it has at least as many neighbours of the opposite colour as of its own colour.
--
--   Then $q$ extends to an unfriendly colouring of all of $G$ if and only if each hub $x$ satisfies at least one of the following conditions.
--
--   1. Infinitely many hub neighbours of $x$ have colour different from $q(x)$.
--   2. There are infinitely many distinct components $C$ for which one can colour $C$ so that every vertex of $C$ is unfriendly, using the fixed boundary colours, and some neighbour of $x$ in $C$ has colour different from $q(x)$.
--
--   The colouring in the second condition may depend on both $x$ and $C$. Component sizes and the numbers of hubs on their boundaries may be unbounded.
-- source:
--   Original component-extension lemma for the unfriendly partition mission in Ten Challenges in Combinatorics, Challenge 10. The local Lean theorem is TenChallenges.Continuation.StableComponents.extension_iff. The canonical challenge is at https://tenchallenges.github.io/ten-challenges/.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
universe u

namespace TenChallenges
theorem challenge_10_stableComponentExtension {V : Type u} [Countable V] (G : SimpleGraph V)
    (q : V → Bool) (hfinite : ∀ C : (G.induce {v : V | (G.neighborSet v).Finite}).ConnectedComponent, C.supp.Finite) :
    let I : Set V := {v | (G.neighborSet v).Infinite}
    (∃ c : V → Bool, Set.EqOn c q I ∧ ∀ v, UnfriendlyAt G (fun w => some (c w)) v) ↔
      ∀ x ∈ I, ({y : V | G.Adj x y ∧ q y ≠ q x} ∩ I).Infinite ∨
        {C : (G.induce {v : V | (G.neighborSet v).Finite}).ConnectedComponent |
          ∃ d : V → Bool,
            (Set.EqOn d q I ∧ ∀ y ∈ C.supp, UnfriendlyAt G (fun w => some (d w)) y.val) ∧
            ∃ y ∈ C.supp, G.Adj x y.val ∧ d y.val ≠ q x}.Infinite := by sorry
end TenChallenges
