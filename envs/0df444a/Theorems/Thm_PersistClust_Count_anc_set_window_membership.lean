-- Prove2me | Theorems.Thm_PersistClust_Count_anc_set_window_membership
-- name    : PersistClust.Count.anc_set_window_membership
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:37:20.257275+00:00
-- url     : https://prove2.me/theorems/527a2386-ad5b-4734-bc5a-bad7593dc688
-- title:
--   Ancestor transfer across a crit-free window: β + δ is an ancestor level
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Let C be a t-cell with ancestor level u (u ∈ AncSet hLaw t C: some u-cell C' coarsens to C), let δ > 0, and suppose the window [u, β + δ] is free of critical levels (every critical w satisfies w < u or β + δ < w) with u ≤ β + δ. Then β + δ is itself an ancestor level of C: β + δ ∈ AncSet hLaw t C. Proof: the rigid class structure on crit-free windows (critSet_spec from the tameness module) lets the representative point of C' at level u be matched by a point y at level β + δ with J u (rep C') y; the β + δ-class of y is a component at β + δ whose structMap down to u equals C' (both are u-classes of the common representatives, chained through the filtration law's compatibility and transitivity), so composing with the coarsening C' → C (structMap_comp) exhibits a β + δ-cell coarsening to C. This transfer is the mechanism that pushes ancestry strictly past a would-be non-critical birth-supremum, the core of the birth-sup criticality dichotomy.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 ancestor transfer (t3_ancSup_mem in the rankKill master, Scratch_rankR1 L694-740, with inlined helper structMap_comp L77-95) — the window mechanism consumed by t3_birthSup_in_critSet and thus by every band-to-pin census reduction of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem anc_set_window_membership {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t β : ℝ} {C : comps stage J t}
    {u δ : ℝ} (hu : u ∈ AncSet hLaw t C) (hδ : 0 < δ)
    (hav : ∀ w ∈ critSet hTame, w < u ∨ β + δ < w)
    (hule : u ≤ β + δ) :
    β + δ ∈ AncSet hLaw t C
    := by sorry
