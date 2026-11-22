-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_guardedSites
-- name    : TenChallenges.challenge_10_guardedSites
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T20:28:38.406076+00:00
-- url     : https://prove2.me/theorems/8d124302-351b-49e0-9c37-d29a30240801
-- title:
--   Guarded triangles give winning partitions at every ordinal clock
-- statement:
--   Let $G$ be a countable simple graph with disjoint vertex sets $H$ and $Y$. Every vertex of $H$ has infinitely many neighbours in $Y$, and only finitely many vertices outside $H\cup Y$ have infinite degree. Each $y\in Y$ has degree at most six and at least two neighbours in $H$. Suppose each $y$ lies in a triangle $yuw$ where $u\notin H\cup Y$, $w\notin H$, and $u$ has degree three or four. Then Partitioner wins the unfriendly partition game on $G$ from the empty partition at every ordinal clock. The triangles may overlap.
-- source:
--   Intermediate result for Ten Challenges in Combinatorics, Challenge 10, on the unfriendly partition game. Original guarded-site criterion, 22 November 2026.

import Definitions.Def_TenChallenges_Challenge_10
import Mathlib.Data.Set.Card
universe u v

theorem TenChallenges.challenge_10_guardedSites {V : Type u} [Countable V] (G : SimpleGraph V) (H Y : Set V) (disj : Disjoint H Y)
    (few : {v | v ∉ H ∪ Y ∧ (G.neighborSet v).Infinite}.Finite)
    (witnesses : ∀ h ∈ H, (G.neighborSet h ∩ Y).Infinite)
    (small : ∀ y ∈ Y, (G.neighborSet y).encard ≤ 6)
    (anchors : ∀ y ∈ Y, 2 ≤ (G.neighborSet y ∩ H).encard)
    (guards : ∀ y ∈ Y, ∃ u w, u ∉ H ∪ Y ∧ w ∉ H ∧ G.Adj y u ∧ G.Adj y w ∧ G.Adj u w ∧
      ((G.neighborSet u).encard = 3 ∨ (G.neighborSet u).encard = 4))
    (r : Ordinal.{v}) : PartitionerWins G (emptyPartition V) r := by sorry
