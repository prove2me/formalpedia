-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_fiveFibrePieces
-- name    : TenChallenges.challenge_10_fiveFibrePieces
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T20:25:59.463809+00:00
-- url     : https://prove2.me/theorems/95ee75af-14da-4dd8-8f48-70bda4f5a625
-- title:
--   Five supported pieces beyond a hub pair give a protected quota-three extension
-- statement:
--   Let two different vertices in a graph have colour zero and let Y be a set of their common neighbours of colour one. Give both anchors and each site in Y quota at most three. If five pairwise disjoint nonempty pieces outside the anchors and Y each meet all their quotas inside the prescribed set S, the two anchors, Y and their own piece, then some nonempty set of residual vertices already meets all its quotas together with S. The result allows infinite pieces and infinitely many sites.
-- source:
--   Ten Challenges in Combinatorics, Mission 10. Sufficient condition for extending a protected colouring at quota three.

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sum

set_option autoImplicit false

universe u v

theorem TenChallenges.challenge_10_fiveFibrePieces {V : Type u} {I : Type v} (G : SimpleGraph V) (c : V → Bool)
    (S C Y : Set V) (q : V → ℕ) (a b : V) (hab : a ≠ b)
    (L : Finset I) (P : I → Set V) (ha : a ∈ C) (hb : b ∈ C) (hY : Y ⊆ C)
    (hca : c a = false) (hcb : c b = false) (hone : ∀ y ∈ Y, c y = true)
    (hAdj : ∀ y ∈ Y, G.Adj a y ∧ G.Adj b y)
    (hqa : q a ≤ 3) (hqb : q b ≤ 3) (hYq : ∀ y ∈ Y, q y ≤ 3)
    (hP : ∀ i ∈ L, (P i).Nonempty ∧ P i ⊆ C ∧ Disjoint (P i) ({a, b} ∪ Y))
    (hdis : (L : Set I).PairwiseDisjoint P)
    (hquota : ∀ i ∈ L, ∀ x ∈ P i, (q x : ℕ∞) ≤
      {w | w ∈ S ∪ ({a, b} ∪ Y) ∪ P i ∧ G.Adj x w ∧ c w ≠ c x}.encard)
    (hcount : 5 ≤ L.card) :
    ∃ D : Set V, D.Nonempty ∧ D ⊆ C ∧
      ∀ x ∈ D, (q x : ℕ∞) ≤ {w | w ∈ S ∪ D ∧ G.Adj x w ∧ c w ≠ c x}.encard := by sorry
