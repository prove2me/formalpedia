-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_losingInducedBall
-- name    : TenChallenges.challenge_10_losingInducedBall
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T06:23:12.564749+00:00
-- url     : https://prove2.me/theorems/59b308fc-ab3b-4fcf-b4cc-4f51a1d7fa87
-- title:
--   An induced walk ball witnesses a first finite loss (Challenge 10)
-- statement:
--   Let $G$ be a simple graph and let $n$ be a natural number. Assume Partitioner wins from the empty partial partition at every natural clock $m<n$ and loses from the empty partial partition at clock $n$. Then there is a vertex $a$ such that Partitioner also loses from the empty partial partition at clock $n$ on the graph induced by the vertices reachable from $a$ by a walk of length at most $2^n-2$.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10 (https://tenchallenges.github.io/ten-challenges/). This is a finite-clock reduction for its partitioning game.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
universe u v

namespace TenChallenges
theorem challenge_10_losingInducedBall {V : Type u} (G : SimpleGraph V) (n : ℕ)
    (hprev : ∀ m : ℕ, m < n → PartitionerWins G (emptyPartition V) (m : Ordinal.{v}))
    (hloss : ¬ PartitionerWins G (emptyPartition V) (n : Ordinal.{v})) :
    ∃ a : V,
      let B : Set V := {x | ∃ w : G.Walk a x, w.length ≤ 2 ^ n - 2}
      ¬ PartitionerWins (G.induce B) (emptyPartition B) (n : Ordinal.{v}) := by sorry
end TenChallenges
