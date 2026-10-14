-- Prove2me | Theorems.Thm_PersistClust_Count_struct_map_id
-- name    : PersistClust.Count.struct_map_id
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:55:37.223444+00:00
-- url     : https://prove2.me/theorems/86216377-7604-4648-8864-7dbfb34551c3
-- title:
--   The coarsening map at a reflexive order-relation is the identity
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw. For every level t and every t-cell C, the structure map at the reflexive order-relation t ≤ t is the identity: structMap hLaw le_rfl C = C. Proof: structMap sends a cell to the t-class of its chosen representative (compRep), and compRep_spec states that the representative's class is exactly the cell's underlying set; Subtype.ext transports that set equality to equality of components. This trivial-seeming lemma is the anchor that makes the cell's own level an ancestor level of itself, used at the base of every ancestor-set nonemptiness argument in the birth-supremum machinery.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the structMap identity at le_rfl (t3_structMap_id in the rankKill master, Scratch_rankR1 L493-496, no in-file helpers) — consumed by the ancestor-set nonemptiness steps of the meets/rank/birth-sup machinery of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem struct_map_id {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C
    := by sorry
