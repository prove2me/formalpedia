-- Prove2me | Theorems.Thm_TenChallenges_challenge_10_relativeThinning
-- name    : TenChallenges.challenge_10_relativeThinning
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T11:02:22.73333+00:00
-- url     : https://prove2.me/theorems/ef5ed449-f169-4048-8810-1f5d339b081a
-- title:
--   Relative thinning of countable graphs with prescribed finite neighbour quotas
-- statement:
--   Let C be a set of vertices of a countable simple graph whose neighbours lie in S union C. Each vertex v of C requests k(v) neighbours, where k(v) is a natural number at most its degree. There is a spanning subgraph supported on edges meeting C in S union C that satisfies all requests and has finite degree at every vertex of C outside T if and only if every finite set F in C outside T leaves only finitely many vertices v of C outside F with fewer than k(v) neighbours outside F. The set T may be arbitrary.
-- source:
--   Ten Challenges in Combinatorics, Challenge 10. Supplementary lemma for the finite-quota approach to the first infinite clock.

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false

universe u

theorem TenChallenges.challenge_10_relativeThinning {V : Type u} [Countable V] (G : SimpleGraph V)
    (S C T : Set V) (k : V → ℕ)
    (hboundary : ∀ v ∈ C, G.neighborSet v ⊆ S ∪ C)
    (henough : ∀ v ∈ C, (k v : ℕ∞) ≤ (G.neighborSet v).encard) :
    (∀ F : Set V, F.Finite → F ⊆ C \ T →
      {v | v ∈ C ∧ v ∉ F ∧ {w | G.Adj v w ∧ w ∉ F}.encard < (k v : ℕ∞)}.Finite) ↔
    ∃ J : SimpleGraph V, J ≤ G ∧
      (∀ v ∈ C, (k v : ℕ∞) ≤ (J.neighborSet v).encard) ∧
      (∀ w ∈ C \ T, (J.neighborSet w).Finite) ∧
      (∀ v w, J.Adj v w → (v ∈ C ∨ w ∈ C) ∧ v ∈ S ∪ C ∧ w ∈ S ∪ C) := by sorry
