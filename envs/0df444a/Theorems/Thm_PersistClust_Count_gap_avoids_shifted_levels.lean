-- Prove2me | Theorems.Thm_PersistClust_Count_gap_avoids_shifted_levels
-- name    : PersistClust.Count.gap_avoids_shifted_levels
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:25:41.075247+00:00
-- url     : https://prove2.me/theorems/6bb20611-2492-436e-92ee-81e3358a802c
-- title:
--   δ₀-gap avoidance: no cell birth-supremum equals b ± ζ or d ± ζ for ζ inside the gap
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Suppose δ₀-gaps isolate the levels b and d from the critical set: every critical τ ≠ b satisfies δ₀ < |τ − b|, and every critical τ ≠ d satisfies δ₀ < |τ − d|. Then for any ζ ∈ Set.Ioo 0 δ₀, any level t and any t-cell C, the four shifted levels b − ζ, b + ζ, d + ζ, d − ζ are all different from the birth-supremum of C. The reason: every cell's birth-supremum is a critical level (unconditionally — a self-level birth-sup forces the level itself into the critical set); if the birth-sup equaled b − ζ (say), then either it is b, contradicting |b − ζ − b| = ζ < δ₀, or it differs from b, and then the gap δ₀ < |birthSup − b| contradicts |birthSup − b| = ζ < δ₀; the three other shifts are symmetric. This supplies the genericity (avoidance) hypotheses needed by the window-split and box-combination identities.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 avoidance helper (t3_avoidOf in the rankKill master, Scratch_rankR1 L1855-1897) with its full inlined helper chain — structMap_comp L77-95, t3_fresh_in_critSet L400-453, t3_structMap_id L493-496, t3_windowEx L635-690, t3_ancSup_mem L694-740, t3_bSup_self_crit L1030-1048, t3_birthSup_in_critSet L825-861, t3_bSup_in_crit L1052-1057 — the genericity supplier for the window-split and box-identity sites of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem gap_avoids_shifted_levels {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d δ₀ : ℝ}
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    {ζ : ℝ} (hζ : ζ ∈ Set.Ioo (0 : ℝ) δ₀) (t : ℝ) (C : comps stage J t) :
    b - ζ ≠ birthSup hLaw t C ∧ b + ζ ≠ birthSup hLaw t C ∧
      d + ζ ≠ birthSup hLaw t C ∧ d - ζ ≠ birthSup hLaw t C
    := by sorry
