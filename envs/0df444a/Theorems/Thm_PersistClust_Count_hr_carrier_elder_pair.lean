-- Prove2me | Theorems.Thm_PersistClust_Count_hr_carrier_elder_pair
-- name    : PersistClust.Count.hr_carrier_elder_pair
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T15:09:08.109176+00:00
-- url     : https://prove2.me/theorems/5c2ce2ff-5b70-4d0f-9dfe-1b10c19b3f38
-- title:
--   Carrier-elder pigeonhole: a bar of nonzero multiplicity has two distinct pin cells (one b-band, one at least b-band) whose below-descents coincide
-- statement:
--   For a tame filtration module (a filtered stage family stage with a comparison relation J satisfying the filtration law, with birthSup the supremum of levels at which a cell has an ancestor, critSet the critical levels, mult the bar multiplicity of the rank diagram, and structMap the level-descent map on components), let (b, d) be a bar with d < b whose multiplicity mult (rankFn) ((b, d)) is nonzero, suppose the critical levels stay δx-far from b and from d (except possibly at the points themselves), and let η₀ be a pin offset with 0 < η₀ < δx smaller than half the bar width. Then at the pin level d + η₀ there are two DISTINCT cells C₁ and C₂ such that C₁ is b-band (its birth-supremum is exactly b), C₂ is at least b-band (b ≤ birthSup C₂), and the two cells co-merge below: their descents to the level d − η₀ are equal. This is the census-surplus pigeonhole of the carrier-elder dichotomy: nonzero multiplicity forces the b-band census at the pin to strictly outnumber the b-band census below (the comb bracket t3_comb at the pin minus the bracket below is at least 1), and the surplus is realized either by a MERGE (two distinct b-band pin cells with equal below-descents, since an injective descent map would contradict Set.encard_le_encard_of_injOn) or by an ABSORB (some b-band pin cell descends off-band below with birthSup > b by monotonicity, and its below-cell's ancestor ray furnishes an ancestor above b whose pin-level descent is a distinct elder cell with birthSup at least b, co-merging with the carrier at d − η₀ via structMap_comp).
-- source:
--   Support tool of the persistence-clustering deliverable (hr-route step 3, carrierE2 fill, rankKill master Scratch_rankR1 L4008-4141): the census-surplus pigeonhole delivering the carrier/elder pair — the only new content of the sync route — consumed directly by the sync-pair co-merge wiring (sync_comerge_images) and the pair-lift satellite (image birth band pin machinery).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem hr_carrier_elder_pair {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d δx η₀ : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δx < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δx < |τ - d|))
    (hη₀ : η₀ ∈ Set.Ioo (0 : ℝ) δx) (hη₀bd : η₀ < (b - d) / 2)
    (hmult : mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0) :
    ∃ C₁ C₂ : comps stage J (d + η₀),
      birthSup hLaw (d + η₀) C₁ = b ∧ b ≤ birthSup hLaw (d + η₀) C₂ ∧ C₁ ≠ C₂ ∧
      structMap hLaw (show d - η₀ ≤ d + η₀ by linarith [hη₀.1]) C₁
        = structMap hLaw (show d - η₀ ≤ d + η₀ by linarith [hη₀.1]) C₂
    := by sorry
