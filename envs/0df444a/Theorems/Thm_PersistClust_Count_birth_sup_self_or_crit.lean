-- Prove2me | Theorems.Thm_PersistClust_Count_birth_sup_self_or_crit
-- name    : PersistClust.Count.birth_sup_self_or_crit
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:34:09.239215+00:00
-- url     : https://prove2.me/theorems/0da2f3eb-dbd5-4d70-9440-e4632efd8415
-- title:
--   A cell's birth-supremum either equals its own level or lies in the critical set
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. For every level t and every t-cell C, either the birth-supremum of C equals t itself, or the birth-supremum lies in the critical set: birthSup hLaw t C = t ∨ birthSup hLaw t C ∈ (critSet hTame : Set ℝ). Proof: split on whether some ancestor level strictly exceeds t. If so and the birth-sup β were non-critical, the window existence lemma (t3_windowEx) produces an ancestor level u above every critical level below β and a δ > 0 with [u, β + δ] crit-free; the ancestor transfer (t3_ancSup_mem) then places β + δ itself in the ancestor-level set, contradicting that β is its supremum. If no ancestor level strictly exceeds t, then every ancestor level is ≤ t, so the supremum birthSup = sSup (AncSet) is ≤ t, and since t is itself an ancestor level (structMap is the identity at t), birthSup = t. Together with the self-level case (a self-level birth-sup forces the level into the critical set) this yields the unconditional criticality of every birth-supremum.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 birth-sup dichotomy (t3_birthSup_in_critSet in the rankKill master, Scratch_rankR1 L825-861) with its inlined helper chain — structMap_comp L77-95, t3_structMap_id L493-496, t3_windowEx L635-690, t3_ancSup_mem L694-740 — the substantive half of the unconditional birth-sup criticality consumed by the band-to-pin census reductions of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem birth_sup_self_or_crit {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    (t : ℝ) (C : comps stage J t) :
    birthSup hLaw t C = t ∨ birthSup hLaw t C ∈ (critSet hTame : Set ℝ)
    := by sorry
