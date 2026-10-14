-- Prove2me | Theorems.Thm_PersistClust_Count_meets_iff_birth_sup
-- name    : PersistClust.Count.meets_iff_birth_sup
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:02:24.404876+00:00
-- url     : https://prove2.me/theorems/5f9dd66a-758d-49d8-af9e-e1330666ca16
-- title:
--   A cell meets the stage at s iff its birth-supremum strictly exceeds s
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. For real levels t ≤ s such that s differs from the birth-supremum of every t-cell (hs), a t-cell C meets the stage image at s — i.e. C.val belongs to the image of stage s under x ↦ {y | J t x y} — if and only if s is strictly below the birth-supremum of C: C.val ∈ ((fun x => {y | J t x y}) '' stage s) ↔ s < birthSup hLaw t C. Forward: the s-class of a witnessing point x ∈ stage s is a component at s whose structMap down to t is C, so s is an ancestor level of C, giving s ≤ sSup (AncSet) = birthSup with equality excluded by hs. Backward: s < birthSup produces, by the supremum property of the ancestor-level set, an ancestor level u > s with a u-cell mapping to C; the representative point of that cell lies in stage s by antitonicity and its t-class is exactly C.val (t3_desc_point).
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 meets-birthSup equivalence (t3_meets_birthSup in the rankKill master, Scratch_rankR1 L525-576, with inlined helpers t3_structMap_id L493-496 and t3_desc_point L500-521) — the cell-wise bridge that converts the rank's stage-image membership into a birth-supremum inequality, consumed by the rank identity and the window-split machinery of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem meets_iff_birth_sup {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {s t : ℝ} (hst : t ≤ s)
    (hs : ∀ C : comps stage J t, s ≠ birthSup hLaw t C) (C : comps stage J t) :
    C.val ∈ ((fun x => {y | J t x y}) '' stage s) ↔ s < birthSup hLaw t C
    := by sorry
