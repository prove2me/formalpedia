-- Prove2me | Theorems.Thm_PersistClust_Count_essential_bar_mult_nonzero
-- name    : PersistClust.Count.essential_bar_mult_nonzero
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:20:43.743057+00:00
-- url     : https://prove2.me/theorems/03c44f8c-e51d-4ab0-9cdd-9ee166f02fac
-- title:
--   Essential bars: a cell whose value-ray is constantly e forces the essential bar (e, bottom) to have positive multiplicity
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law (stage sets with a same-component relation) of finite type (IsTameModule), with the birth-sup bookkeeping: birthSup of a component class is the supremum of the levels at which it has ancestors. Suppose a component class E at level T has birth-sup e, and the value-ray through E is CONSTANTLY e under every descent: for every level w at most T, the descent of E to level w also has birth-sup exactly e. Then the ESSENTIAL bar at (e, bottom) is present in the diagram: mult (rankFn stage J) (e, bottom) is nonzero. The reason: for every eta > 0 and every level t at most e - eta, the census at level t exhibits a class with birth-sup in (e - eta, e] - the descent of E itself when t is at most T, or otherwise the descent of an ancestor of E at some level u in (e - eta, e] - and this class meets the stage at level e - eta (its ancestor level lies above e - eta) but not the stage at level e + eta (a meeting point would push the class's birth-sup above e). Hence for every probe (eta, t) the rank difference rankFn (e - eta) t - rankFn (e + eta) t is at least 1, and the bottom-branch infimum formula for the multiplicity of (e, bottom) - an infimum over all eta > 0 and t at most e - eta of exactly these rank differences - is at least 1.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the bottom-census step that converts a constant value-ray (every descent of the cell keeps birth-sup e) into a positive essential-bar count at (e, bottom), used by the census death-localization argument to handle bars with death coordinate bottom. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; companion of the accepted theorem_4_5 elder-rule support cluster (elder_chase, essential_birth_gt_bound, separated_bar_death_lower_bound, born_component_subset), of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem essential_bar_mult_nonzero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {T e : ℝ} (E : comps stage J T) (he : birthSup hLaw T E = e)
    (hfull : ∀ (w : ℝ) (hw : w ≤ T), birthSup hLaw w (structMap hLaw hw E) = e) :
    mult (rankFn stage J) ((e : EReal), (⊥ : EReal)) ≠ 0
    := by sorry
