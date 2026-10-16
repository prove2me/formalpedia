-- Prove2me | Theorems.Thm_PersistClust_Count_hall_of_classes
-- name    : PersistClust.Count.hall_of_classes
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T20:53:12.942374+00:00
-- url     : https://prove2.me/theorems/10c0065c-c41f-4941-a8bc-23de4f67b38e
-- title:
--   Hall's condition glues over a partition: per-class Hall bounds with fibers disjoint across classes give the Hall bound for every finite set
-- statement:
--   Let S, T, K be types, k : S -> K a class map and G : S -> Set T a family of fibers such that fibers of elements in different classes are disjoint. If every finite set s of S contained in a single class satisfies encard s <= encard (union of G x over x in s), then every finite set s of S satisfies the same bound. Used to assemble a global Hall condition (hence, with finite fibers, an injective choice) from per-class interval-Hall bounds, e.g. per birth value or per death value in persistence matchings.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorems 4.5 / 4.8 cluster): the gluing step of the Bauer-Lesnick induced-matching route (per-birth and per-death Hall bounds assembled into a global one). Pure Mathlib.

import Mathlib

namespace PersistClust.Count

theorem hall_of_classes {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅)
    (hclass : ∀ s : Set S, s.Finite → (∀ a ∈ s, ∀ a' ∈ s, κ a = κ a') →
      s.encard ≤ (⋃ x ∈ s, G x).encard) :
    ∀ s : Set S, s.Finite → s.encard ≤ (⋃ x ∈ s, G x).encard
    := by sorry
