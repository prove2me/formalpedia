-- Prove2me | Theorems.Thm_PersistClust_Count_t5_imageBirthLower
-- name    : PersistClust.Count.t5_imageBirthLower
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:35:18.926226+00:00
-- url     : https://prove2.me/theorems/ebb9cd8d-64ba-40e4-ba2d-814ea1183ff5
-- title:
--   Image-birth lower bound: the phi-image cell at level beta - eps is born no later than that level
-- statement:
--   The interleaving setup: a tame Y-module of finite components under a filtration law; phi maps X-levels down eps to Y-levels. For an X-cell C at a level beta at least alpha, the birth-supremum of the image cell phi_beta C at the pullback level beta - eps is at least beta - eps: the level itself is an ancestor level of the image cell, and a cell's birth-sup is the supremum of its ancestor levels.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the image-birth lower bound of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem t5_imageBirthLower {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawY : FiltrationLaw stageY JY) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    {β : ℝ} (hβ : α ≤ β) (C : comps stageX JX β) :
    β - ε ≤ birthSup hLawY (β - ε) (φ β hβ C)
    := by sorry
