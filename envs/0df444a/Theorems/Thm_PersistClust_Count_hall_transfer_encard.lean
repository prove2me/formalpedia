-- Prove2me | Theorems.Thm_PersistClust_Count_hall_transfer_encard
-- name    : PersistClust.Count.hall_transfer_encard
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-16T04:15:48.282047+00:00
-- url     : https://prove2.me/theorems/18535b14-3e13-4dc2-abac-33058db64542
-- title:
--   Hall's inequality transfers along injective relabellings that preserve neighbourhoods
-- statement:
--   Let vA : A -> C and vB : B -> C be injective, GA : A -> Set T and GB : B -> Set T neighbourhood maps, sA a set of A and sB a set of B with vA(sA) = vB(sB), and suppose GA a = GB b whenever vA a = vB b. If |sB| <= |union over b in sB of GB b| (cardinalities as encard), then |sA| <= |union over a in sA of GA a|.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): moves Hall conditions between two indexings of the same demand set in the induced-matching route. Pure Mathlib.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem hall_transfer_encard {A B C T : Type} (vA : A → C) (vB : B → C)
    (hA : Function.Injective vA) (hB : Function.Injective vB)
    (GA : A → Set T) (GB : B → Set T) (sA : Set A) (sB : Set B)
    (himg : vA '' sA = vB '' sB) (hG : ∀ a b, vA a = vB b → GA a = GB b)
    (h : sB.encard ≤ (⋃ b ∈ sB, GB b).encard) :
    sA.encard ≤ (⋃ a ∈ sA, GA a).encard
    := by sorry
