-- Prove2me | Theorems.Thm_PersistClust_Count_census_band_reduction
-- name    : PersistClust.Count.census_band_reduction
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:11:02.403657+00:00
-- url     : https://prove2.me/theorems/1f3bb13c-a6d6-41ff-8b09-377101036d03
-- title:
--   Census reduction: inside the δ₀-gap the open b-band census collapses to the pinned birth-sup = b census
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Let b be a real level, η a radius with η ∈ Set.Ioo 0 δ₀, and assume the gap hypothesis hδ₀b: every critical level τ ≠ b satisfies δ₀ < |τ − b|. Then at every level v the open-band census — the set of v-cells whose birth-supremum lies in the window (b − η, b + η) — equals the pinned census: {C : comps stage J v | b − η < birthSup hLaw v C ∧ birthSup hLaw v C < b + η} = {C : comps stage J v | birthSup hLaw v C = b}. The reason: every cell's birth-supremum lies in the critical set (unconditionally — the self-level case is itself forced into the critical set, otherwise freshness would push the birth-sup strictly above the cell's own level), and the gap hypothesis excludes every critical value other than b from the window, so a birth-sup inside the window must be exactly b. This is the set-reduction step that converts band censuses into pinned censuses throughout the matching-census assembly.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 census reduction (t3_census_red in the rankKill master, Scratch_rankR1 L1844-1852) with its full inlined helper chain — structMap_comp L77-95, t3_fresh_in_critSet L400-453, t3_structMap_id L493-496, t3_windowEx L635-690, t3_ancSup_mem L694-740, t3_bSup_self_crit L1030-1048, t3_birthSup_in_critSet L825-861, t3_bSup_in_crit L1052-1057, t3_win_beta L1061-1076 — the band-to-pin conversion consumed by the combination stability and drop sites of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem census_band_reduction {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b η δ₀ v : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hδ₀b : ∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) :
    ({C : comps stage J v | b - η < birthSup hLaw v C ∧ birthSup hLaw v C < b + η} :
      Set (comps stage J v))
      = {C : comps stage J v | birthSup hLaw v C = b}
    := by sorry
