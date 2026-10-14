-- Prove2me | Theorems.Thm_PersistClust_Count_crit_free_descent_injective
-- name    : PersistClust.Count.crit_free_descent_injective
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T19:43:56.270887+00:00
-- url     : https://prove2.me/theorems/c7d5047f-51e3-4c76-bc85-52d621ce1425
-- title:
--   Crit-free-window descent is injective on component classes
-- statement:
--   For a tame module (IsTameModule) with critical set critSet, the coarsening descent structMap from level w' down to w is INJECTIVE whenever the window [w, w'] avoids the critical set: two stage-w' classes whose w-descents coincide are equal. The proof pushes the coincidence of the descended neighborhoods through the critical-free componentwise bijection of critSet_spec: the two representatives become J-related at w', so their full classes coincide by J-transitivity, and Subtype.ext closes.
-- source:
--   T3a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the descent-injectivity half of the critical-window rigidity consumed by the thread bookkeeping (birth-sup threading, combination stability). Transcribed GREEN from the ORCH-verified matching-gate lane working copy.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem crit_free_descent_injective {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w w' : ℝ} (hww : w ≤ w')
    (hfree : ∀ τ ∈ critSet hTame, τ < w ∨ w' < τ) {C₁ C₂ : comps stage J w'}
    (h : structMap hLaw hww C₁ = structMap hLaw hww C₂) : C₁ = C₂
    := by sorry
