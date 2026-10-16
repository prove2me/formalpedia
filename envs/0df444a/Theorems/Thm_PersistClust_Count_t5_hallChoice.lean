-- Prove2me | Theorems.Thm_PersistClust_Count_t5_hallChoice
-- name    : PersistClust.Count.t5_hallChoice
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:37:23.479457+00:00
-- url     : https://prove2.me/theorems/e69b459c-bb35-44c0-86bb-c817d8f8b4b7
-- title:
--   Infinite Hall marriage by finite reduction: finite fibers and the finite-subset Hall condition give an injective choice function
-- statement:
--   Let G assign to every point a of a type S a finite set of choices G a. If every finite demand subset s satisfies the Hall inequality -- the encard of s is at most the encard of the union of the fibers over s -- then there is a globally injective choice function f : S -> T with f a in G a for every a. The statement and proof are fully Mathlib-native: the reduction passes through the finite Hall marriage theorem applied to the toFinsets of the fibers.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the infinite hall marriage by finite reduction of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_hallChoice {S T : Type} (G : S → Set T)
    (hfin : ∀ a, (G a).Finite)
    (hhall : ∀ s : Set S, s.Finite → s.encard ≤ (⋃ x ∈ s, G x).encard) :
    ∃ f : S → T, Function.Injective f ∧ ∀ a, f a ∈ G a
    := by sorry
