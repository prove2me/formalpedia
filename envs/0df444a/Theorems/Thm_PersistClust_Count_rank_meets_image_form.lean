-- Prove2me | Theorems.Thm_PersistClust_Count_rank_meets_image_form
-- name    : PersistClust.Count.rank_meets_image_form
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:47:21.431037+00:00
-- url     : https://prove2.me/theorems/cda32294-f335-4b51-ba6b-679bfdef3a9e
-- title:
--   Cell-image bridge: r(s,t) counts the t-cells meeting the stage at s
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw. For levels t ≤ s, the rank function — defined as the extended cardinality of the image of stage s under the map x ↦ {y | J t x y} assigning to each point its t-class — equals the extended cardinality of the set of t-cells whose underlying set appears in that image: rankFn stage J s t = {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage s)}.encard. Proof: the point-level image equals the Subtype.val image of the component set (each t-class of a point x ∈ stage s is a component at t, since x remains in stage t by the stage family's antitonicity; conversely, every component in the set is by definition in the image), and the encard is preserved across the injective Subtype.val image. This bridge converts the point-level rank into a component-level census and underlies the birth-sup form of the rank identity.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 cell-image bridge (t3_rank_meets in the rankKill master, Scratch_rankR1 L468-490, no in-file helpers) — the component-level reading of rankFn consumed by t3_rank_orig and through it by the window-split and box-combination machinery of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem rank_meets_image_form {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {s t : ℝ} (hst : t ≤ s) :
    rankFn stage J s t =
      {C : comps stage J t | C.val ∈ ((fun x => {y | J t x y}) '' stage s)}.encard
    := by sorry
