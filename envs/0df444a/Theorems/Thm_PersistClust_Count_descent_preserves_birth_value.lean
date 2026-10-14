-- Prove2me | Theorems.Thm_PersistClust_Count_descent_preserves_birth_value
-- name    : PersistClust.Count.descent_preserves_birth_value
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T20:08:31.379601+00:00
-- url     : https://prove2.me/theorems/726f8515-a849-49f3-9303-fc6bf3c12bf5
-- title:
--   Descents across critical-value-free windows preserve the birth value
-- statement:
--   For a tame persistence module, let C be a component class at level s and let t ≤ s be a lower level such that the window between them is free of critical values (every critical value u of the module satisfies u < t or s < u). Then descending C to level t preserves its birth value: the birth-supremum of the descended class equals the birth-supremum of the original class. This is the value-constancy step of the T3a analysis: a cell's birth value can only change across a window that contains a critical value.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the T3a-value constancy lemma — descending a cell across a critical-value-free window preserves its birth value (t3_value_const in the rankKill master, Scratch_rankR1 L3927), consumed by the death-side case analyses of the rank-level kill.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem descent_preserves_birth_value {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t s : ℝ} (hts : t ≤ s)
    (hgap : ∀ u ∈ critSet hTame, u < t ∨ s < u)
    (C : comps stage J s) :
    birthSup hLaw t (structMap hLaw hts C) = birthSup hLaw s C
    := by sorry
