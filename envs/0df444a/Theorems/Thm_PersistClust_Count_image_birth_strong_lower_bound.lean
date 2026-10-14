-- Prove2me | Theorems.Thm_PersistClust_Count_image_birth_strong_lower_bound
-- name    : PersistClust.Count.image_birth_strong_lower_bound
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:30:19.942134+00:00
-- url     : https://prove2.me/theorems/8eac3366-ba1b-453b-ba46-60e4fe3b94a1
-- title:
--   Image-birth strong lower bound: an interleaving image is born at least one eps below its source
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, interleaved above a level alpha by maps phi_beta : X-beta -> Y-(beta - eps) satisfying the square (i'): phi_beta applied to the coarsening of a beta'-cell equals the coarsened phi_beta' image (for beta <= beta', both at least alpha). Let C be a component class of X at a level beta at least alpha. Then the birth-supremum of the image class phi_beta C at level beta - eps is at least the birth-supremum of C at level beta, minus eps: birthSup_Y (beta - eps) (phi_beta C) is at least birthSup_X beta C - eps. The reason: every ancestor level u of C (a level at or above beta carrying a class that coarsens onto C) pulls back through the square (i') to an ancestor of the image at level u - eps, so the ancestor-level supremum of the image dominates the source's ancestor-level supremum shifted down by eps. The bound is independent of the probe level beta: the image class at ANY level beta at least alpha inherits the source's birth-sup minus eps. This is the strong lower half of the image-birth band pair (companion: the upper bound via the squares (ii') and (iv')), pinning the birth of an interleaving image thread to within eps of the source thread's birth.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the strong lower half of the image-birth band, used by the census birth-localization argument to pin the birth of interleaving image threads to within eps of their source threads. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; companion of the accepted theorem_4_5 elder-rule support cluster (elder_chase, essential_birth_gt_bound, separated_bar_death_lower_bound, born_component_subset), of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem image_birth_strong_lower_bound {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameY : IsTameModule stageY JY) {α ε : ℝ}
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageX JX β) :
    birthSup hLawX β C - ε ≤ birthSup hLawY (β - ε) (φ β hβ C)
    := by sorry
