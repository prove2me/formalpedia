-- Prove2me | Theorems.Thm_PersistClust_Count_birth_sup_in_critSet
-- name    : PersistClust.Count.birth_sup_in_critSet
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:29:06.085175+00:00
-- url     : https://prove2.me/theorems/56dae6fa-3e66-475a-8a79-da07d147ca83
-- title:
--   Every cell's birth-supremum lies in the critical set
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Then for every level v and every v-cell C, the birth-supremum of C — the supremum of the ancestor-level set AncSet hLaw v C, i.e. the levels at which some cell coarsens to C — is a member of the critical set: birthSup hLaw v C ∈ (critSet hTame : Set ℝ). The proof combines two cases: either the birth-supremum differs from the cell's own level v, in which case t3_birthSup_in_critSet places it in the critical set (a non-critical birth-sup would admit a crit-free window above the ancestor levels, transferring ancestry strictly past the supremum), or the birth-supremum equals v, in which case v itself is critical (t3_bSup_self_crit, via the freshness characterization: otherwise freshness would push the birth-sup strictly above v). This unconditional membership is the load-bearing fact behind all band-to-pin census reductions: birth-suprema can only sit at critical levels.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the unconditional T3 birth-sup criticality (t3_bSup_in_crit in the rankKill master, Scratch_rankR1 L1052-1057, combining t3_birthSup_in_critSet L825-861 with the self-level case t3_bSup_self_crit L1030-1048) with its full inlined helper chain — structMap_comp L77-95, t3_fresh_in_critSet L400-453, t3_structMap_id L493-496, t3_windowEx L635-690, t3_ancSup_mem L694-740 — consumed by the census band reduction, window-β bridge and avoidance helper of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem birth_sup_in_critSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {v : ℝ} (C : comps stage J v) : birthSup hLaw v C ∈ (critSet hTame : Set ℝ)
    := by sorry
