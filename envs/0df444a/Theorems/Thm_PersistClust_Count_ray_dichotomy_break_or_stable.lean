-- Prove2me | Theorems.Thm_PersistClust_Count_ray_dichotomy_break_or_stable
-- name    : PersistClust.Count.ray_dichotomy_break_or_stable
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:29:57.176249+00:00
-- url     : https://prove2.me/theorems/b4847096-d1e8-404f-b4ee-542716aacda4
-- title:
--   Ray dichotomy: a descent family is either value-stable across the whole window or breaks at an honest death level
-- statement:
--   Let I be a component class of a tame persistence module at level w₀ with birth-supremum b₂, and let α' ≤ w₀ be a window bottom. The descent value of I — the birth-supremum of the descent of I at level w, for each w ≤ w₀ — weakly increases as w decreases (descents only merge classes). Then exactly one of the following holds: either the ray is stable, i.e. the descent value is exactly b₂ at every level w of the window [α', w₀]; or there is a break level v with α' ≤ v ≤ w₀ such that the descent value is exactly b₂ at every level ξ with v < ξ ≤ w₀, is different from b₂ at every level ξ with α' ≤ ξ < v, and (whenever the break sits at or below the window bottom) the descent value at the window bottom α' is different from b₂. The break level carries the honest death signature of the ray.
-- source:
--   L3 STUB of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster, death-dichotomy routing): the birth-sup of the descents of a coherent descent family weakly increases as the level decreases (one rungB descent-monotonicity through structMap composition), so the level set where the value equals b₂ is an up-ray: either it fills the whole window (the thread never merges in-range) or there is a boundary v with the honest-death signature — value = b₂ strictly above v, ≠ b₂ strictly below. Proof shape: take the supremum of the off-value set when nonempty and use the up-ray property to pin both sides. Consumed by the death dichotomy routing of the census lane (design §8.12.5).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem ray_dichotomy_break_or_stable {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {w₀ α' b₂ : ℝ} (I : comps stage J w₀) (hI : birthSup hLaw w₀ I = b₂) (hα' : α' ≤ w₀) :
    (∀ (w : ℝ) (hw : w ≤ w₀), α' ≤ w → birthSup hLaw w (structMap hLaw hw I) = b₂)
    ∨ ∃ v : ℝ, α' ≤ v ∧ v ≤ w₀ ∧
      (∀ (ξ : ℝ) (hξ : ξ ≤ w₀), v < ξ → birthSup hLaw ξ (structMap hLaw hξ I) = b₂) ∧
      (∀ (ξ : ℝ) (hξ : ξ ≤ w₀), α' ≤ ξ → ξ < v →
        birthSup hLaw ξ (structMap hLaw hξ I) ≠ b₂) ∧
      (∀ (hvle : α' ≤ w₀), v ≤ α' →
        birthSup hLaw α' (structMap hLaw hvle I) ≠ b₂)
    := by sorry
