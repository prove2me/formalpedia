-- Prove2me | Theorems.Thm_PersistClust_Count_self_level_in_critSet
-- name    : PersistClust.Count.self_level_in_critSet
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:31:33.032063+00:00
-- url     : https://prove2.me/theorems/e6649a3e-49fc-48d8-9761-dd882eab6512
-- title:
--   A cell whose birth-supremum is its own level forces that level into the critical set
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. If a cell C at level t has birth-supremum equal to t itself (h : birthSup hLaw t C = t), then t is a critical level: t ∈ critSet hTame. Proof: by the freshness characterization (t3_fresh_in_critSet) it suffices to show that for every level s > t and every s-cell C' coarsening to C, the pair (s, C') is not fresh. But any such s is an ancestor level of C, so s ≤ sSup (AncSet hLaw t C) = birthSup hLaw t C = t (the ancestor set is bounded above by the tameness volume axiom: a level hosting a component has nonempty stage), contradicting s > t. Hence no ancestor above t exists, the cell is fresh at t, and t is critical. Intuition: if t were not critical, the class structure would be rigid on a crit-free window above t and freshness would push the birth-sup strictly above t.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 self-level birth-sup criticality (t3_bSup_self_crit in the rankKill master, Scratch_rankR1 L1030-1048, with inlined helper t3_fresh_in_critSet L400-453) — the self-level case that, combined with t3_birthSup_in_critSet, gives the unconditional birth-sup criticality consumed by the band-to-pin census reductions of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem self_level_in_critSet {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {t : ℝ} {C : comps stage J t}
    (h : birthSup hLaw t C = t) : t ∈ critSet hTame
    := by sorry
