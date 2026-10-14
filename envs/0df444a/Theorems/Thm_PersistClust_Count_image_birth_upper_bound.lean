-- Prove2me | Theorems.Thm_PersistClust_Count_image_birth_upper_bound
-- name    : PersistClust.Count.image_birth_upper_bound
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:24:22.83301+00:00
-- url     : https://prove2.me/theorems/5a628900-f481-4787-8eaf-26f3af8e2778
-- title:
--   Image-birth upper bound: an interleaving image is born at most one eps above its twice-descended source
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, strongly interleaved above a level alpha by maps phi_beta : X-beta -> Y-(beta - eps) and psi_beta : Y-beta -> X-(beta - eps) (eps at least 0) satisfying the squares (ii') and (iv'): (ii') psi_beta applied to the coarsening of a Y-cell equals the coarsened psi image; (iv') psi_(beta-eps) (phi_beta x) equals the double coarsening of x from level beta down to beta - eps - eps. Let C be a component class of X at a level beta (with alpha at most beta and alpha at most beta - eps), and suppose the twice-descended source cell - the coarsening of C from level beta down to level beta - eps - eps - has birth-supremum b. Then the birth-supremum of the image class phi_beta C at level beta - eps is at most b + eps. The reason: every ancestor level u of the image pulls back via psi to a class whose birth-sup is at least u - eps (a class's own level bounds its birth-sup below), whose descent to level beta - eps - eps coincides (by the two squares composed) with the twice-descended source cell, so its birth-sup is capped by b (birth-sups only grow under descent); combining, u is at most b + eps, and the ancestor-level supremum of the image is at most b + eps. This is the upper half of the image-birth band pair (companion: the strong lower bound via square (i')), pinning the birth of an interleaving image thread to within eps of the source thread's birth.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the upper half of the image-birth band, used by the census birth-localization argument to pin the birth of interleaving image threads to within eps of their source threads. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; companion of the accepted theorem_4_5 elder-rule support cluster (elder_chase, essential_birth_gt_bound, separated_bar_death_lower_bound, born_component_subset), of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem image_birth_upper_bound {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {β b : ℝ} (hβ : α ≤ β) (hβε : α ≤ β - ε)
    (C : comps stageX JX β)
    (hDesc : birthSup hLawX ((β - ε) - ε)
        (structMap hLawX (show (β - ε) - ε ≤ β by linarith) C) = b) :
    birthSup hLawY (β - ε) (φ β hβ C) ≤ b + ε
    := by sorry
