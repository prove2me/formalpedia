-- Prove2me | Theorems.Thm_PersistClust_Count_fresh_in_critSet
-- name    : PersistClust.Count.fresh_in_critSet
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T15:22:43.024693+00:00
-- url     : https://prove2.me/theorems/5cdaafce-095f-4bba-8495-7188545bbbc8
-- title:
--   A fresh class's level is critical
-- statement:
--   In a tame module, if the class C at level τ is fresh (IsFresh hLaw τ C: no class at any level s > τ descends to C), then τ belongs to the critical set critSet hTame: every level carrying a fresh class is a critical level.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): fresh-cell critSet membership (T3-crit) — the fact that fresh levels are critical, used to force census drops to land on critical levels in the rank-level kill (rankR1).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem fresh_in_critSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {τ : ℝ} {C : comps stage J τ} (h : IsFresh hLaw τ C) : τ ∈ critSet hTame
    := by sorry
