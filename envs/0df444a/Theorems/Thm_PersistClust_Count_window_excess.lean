-- Prove2me | Theorems.Thm_PersistClust_Count_window_excess
-- name    : PersistClust.Count.window_excess
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T15:20:03.73476+00:00
-- url     : https://prove2.me/theorems/e2a909ff-9cde-48b1-a6a2-27b674451f5e
-- title:
--   Crit-free window above an ancestor level below a non-critical birth-supremum
-- statement:
--   Let C be a cell class at level t of a tame module, with nonempty and bounded-above ancestor set, whose birth-supremum β equals birthSup hLaw t C and is not a critical level, and suppose some ancestor level lies strictly above t. Then there exist an ancestor level u in AncSet hLaw t C and a positive δ such that every critical level w satisfies w < u or β + δ < w: the window from the ancestor level u up to β + δ (past the birth-supremum) is free of critical levels.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the window-excess existence lemma (T3-window) of the comb family — below a non-critical birth-supremum it cuts a crit-free window [u, β+δ] with an ancestor level at its base, the corridor through which the comb and census-transfer lemmas run in the rank-level kill (rankR1).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem window_excess {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {t β : ℝ} {C : comps stage J t}
    (hBne : (AncSet hLaw t C).Nonempty) (hBdd : BddAbove (AncSet hLaw t C))
    (hβ : β = birthSup hLaw t C) (hβcrit : β ∉ (critSet hTame : Set ℝ))
    (hstrict : ∃ u, u ∈ AncSet hLaw t C ∧ t < u) :
    ∃ u δ : ℝ, 0 < δ ∧ u ∈ AncSet hLaw t C ∧
      (∀ w ∈ critSet hTame, w < u ∨ β + δ < w)
    := by sorry
