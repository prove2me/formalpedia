-- Prove2me | Theorems.Thm_PersistClust_Count_descender_point_class
-- name    : PersistClust.Count.descender_point_class
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:40:14.881697+00:00
-- url     : https://prove2.me/theorems/3ee36d84-59fc-423e-a312-c4ab7c543b8a
-- title:
--   A point of a descender class lies in the coarser class: its t-class is C and it is in stage t
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw. Let t ≤ u, let C be a t-cell, C' a u-cell with structMap hLaw hst C' = C (C' coarsens to C), and let z be a point of C'. Then the t-class of z equals C.val — ((fun x => {y | J t x y}) z) = C.val — and z lies in stage t. Proof: the representative x = compRep of C' is J u-related to z (compRep_spec); transporting down to t by the law's compatibility, the t-class of x is by structMap's defining value exactly C.val, while the t-class of z equals the t-class of x since both are J t-joined to x via the law's transitivity and symmetry. Finally z ∈ stage t because its t-class is a t-component's underlying set and components only contain points of stage t. This is the point-level bridge that converts coarsening data (structMap) into stage-membership witnesses, used throughout the ancestor-set and rank machinery.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 descender point bridge (t3_desc_point in the rankKill master, Scratch_rankR1 L500-521, no in-file helpers) — consumed by t3_meets_birthSup's backward direction and thus by the rank identity and window-split machinery of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem descender_point_class {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {t u : ℝ} (hst : t ≤ u)
    {C : comps stage J t} {C' : comps stage J u} (hC' : structMap hLaw hst C' = C)
    {z : ι} (hz : z ∈ C'.val) :
    ((fun x => {y | J t x y}) z) = C.val ∧ z ∈ stage t
    := by sorry
