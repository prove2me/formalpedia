-- Prove2me | Theorems.Thm_PersistClust_Count_census_self_transfer
-- name    : PersistClust.Count.census_self_transfer
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T09:52:07.590976+00:00
-- url     : https://prove2.me/theorems/114f02e6-ea31-4eb4-9d0e-0dd2342ab615
-- title:
--   Count transfer over a crit-free window: the birth-sup b census is level-invariant
-- statement:
--   Let ι be a type, stage : ℝ → Set ι a stage family and J : ℝ → ι → ι → Prop a relation family satisfying the filtration law hLaw and the tameness module axioms hTame. Let v₁ ≤ v₂ be levels whose window [v₁, v₂] is free of critical levels (every critical τ satisfies τ < v₁ or v₂ < τ), and let b be a level different from both window endpoints. Then the pinned censuses agree: the number of v₁-cells whose birth-supremum equals b equals the number of v₂-cells whose birth-supremum equals b — {C : comps stage J v₁ | birthSup hLaw v₁ C = b}.encard = {C : comps stage J v₂ | birthSup hLaw v₂ C = b}.encard. Proof: the coarsening map structMap (v₁ ≤ v₂) restricts to an injection of the v₂-pinned cells into the v₁-pinned cells (birth-sup is thread-invariant across the crit-free window descent by t3_bSupThread, and the coarsening is injective on crit-free windows by t3_crit_inj), while the section supplied by the surjectivity of the coarsening (t3_desc_surj: in a crit-free window every v₁-cell is the image of some v₂-cell) injects the v₁-pinned census into the v₂-pinned census; the two encard inequalities combine by antisymmetry.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the T3 count transfer (t3_selfTrans in the rankKill master, Scratch_rankR1 L1080-1107) with its inlined helper chain — structMap_comp L77-95, t3_structMap_id L493-496, t3_crit_inj L743-764, t3_bSupThread L769-822, t3_desc_surj L1002-1026 — the level-invariance of the pinned census consumed by the window-count invariance sites of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem census_self_transfer {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {v₁ v₂ : ℝ} (hvv : v₁ ≤ v₂)
    (hfree : ∀ τ ∈ critSet hTame, τ < v₁ ∨ v₂ < τ)
    {b : ℝ} (hfb₁ : v₁ ≠ b) (hfb₂ : v₂ ≠ b) :
    {C : comps stage J v₁ | birthSup hLaw v₁ C = b}.encard
      = {C : comps stage J v₂ | birthSup hLaw v₂ C = b}.encard
    := by sorry
