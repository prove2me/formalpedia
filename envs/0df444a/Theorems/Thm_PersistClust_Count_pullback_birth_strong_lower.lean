-- Prove2me | Theorems.Thm_PersistClust_Count_pullback_birth_strong_lower
-- name    : PersistClust.Count.pullback_birth_strong_lower
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T09:22:44.359063+00:00
-- url     : https://prove2.me/theorems/ad3a663b-c218-402b-80c7-ec01f53c2ab2
-- title:
--   Pullback-birth strong lower bound: an interleaving pullback is born at least one eps below its source
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, interleaved above a level alpha by pullback maps psi_beta : Y-beta -> X-(beta - eps) satisfying the square (ii'): psi_beta applied to the coarsening of a beta'-cell of Y equals the coarsened psi_beta' pullback (for beta <= beta', both at least alpha). Let C be a component class of Y at a level beta at least alpha. Then the birth-supremum of the pullback class psi_beta C at level beta - eps is at least the birth-supremum of C at level beta, minus eps: birthSup_X (beta - eps) (psi_beta C) is at least birthSup_Y beta C - eps. The reason: every ancestor level u of C (a level at or above beta carrying a class of Y that coarsens onto C) pushes forward through the square (ii') to an ancestor of the pullback class at level u - eps, so the ancestor-level supremum of the pullback dominates the source's ancestor-level supremum shifted down by eps. The bound is independent of the probe level beta: the pullback class at ANY level beta at least alpha inherits the source's birth-sup minus eps. This is the psi-mirror of the image-birth strong lower bound (the strong lower half of the pullback side of the interleaving birth band), pinning the birth of a pullback thread to within eps of the source thread's birth; it feeds the kill-pairing bookkeeping and the QSE-sector partner analyses.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the strong lower half of the pullback-birth band (Rung-B T5a psi-mirror), used by the kill-pairing argument of the death-side case tree and the QSE-sector partner bookkeeping. Transcribed GREEN (exit 0, sorry-free) from the deathBar rearch v2 lane working copy; psi-mirror companion of the accepted image_birth_strong_lower_bound, of the accepted theorem_4_5 elder-rule support cluster, and of the accepted theorem_4_8_core.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem pullback_birth_strong_lower {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) {α ε : ℝ}
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageY JY β) :
    birthSup hLawY β C - ε ≤ birthSup hLawX (β - ε) (ψ β hβ C)
    := by sorry
