-- Prove2me | Theorems.Thm_PersistClust_Count_diagram_sync_high_separation
-- name    : PersistClust.Count.diagram_sync_high_separation
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:13:30.092984+00:00
-- url     : https://prove2.me/theorems/bc01f5c0-f12d-4deb-82f8-e9b3075069f5
-- title:
--   Sync-high: distinct 2eps-descents force distinct interleaving images (square (iv') contrapositive)
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, strongly interleaved above a level alpha by maps phi_beta : X-beta -> Y-(beta - eps) and psi_beta : Y-beta -> X-(beta - eps) with eps at least 0, satisfying the square (iv'): for beta at least alpha with alpha at most beta - eps, psi_(beta-eps) (phi_beta x) equals the double coarsening of x from level beta down to level beta - eps - eps. If two cells C1, C2 at a level u (at least alpha, with alpha at most u - eps) have DISTINCT images under the double descent to level u - eps - eps, then their phi-images at level u - eps are DISTINCT. Indeed, if the images coincided, applying the square (iv') to each cell would express both double descents as psi applied to the same image cell, forcing them to coincide - a contradiction. Together with the companion sync-low transfer (co-merging X-cells have co-merging images one eps-band lower) this localizes the merge level of interleaving image threads into the window [delta - eps, delta + eps] around the source merge level delta.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the separation half of the merge-sync pair used to localize the merge level of interleaving image threads to the window [delta - eps, delta + eps] in the census death-localization argument. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; companion of the accepted theorem_4_5 elder-rule support cluster (elder_chase, essential_birth_gt_bound, separated_bar_death_lower_bound, born_component_subset), of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem diagram_sync_high_separation {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {u : ℝ} (hαu : α ≤ u) (hβε : α ≤ u - ε) (hle : u - ε - ε ≤ u)
    (C₁ C₂ : comps stageX JX u)
    (hne : structMap hLawX hle C₁ ≠ structMap hLawX hle C₂) :
    φ u hαu C₁ ≠ φ u hαu C₂
    := by sorry
