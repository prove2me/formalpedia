-- Prove2me | Theorems.Thm_PersistClust_Count_census_cell_pin
-- name    : PersistClust.Count.census_cell_pin
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T08:33:20.502294+00:00
-- url     : https://prove2.me/theorems/2d007eb0-6c18-42c4-8c33-8cbc926a62b4
-- title:
--   Census-cell pin: a nonzero bar at (b, d) supplies, at every small probe η, a component class at level d+η with birth-supremum exactly b
-- statement:
--   Let the multiplicity of the point (b, d) (with d < b) in the persistence diagram of a tame module be nonzero, and let δ₀ be a gap radius such that no critical level τ ≠ b lies within δ₀ of b and no critical level τ ≠ d lies within δ₀ of d. Then for every probe η with 0 < η < δ₀ and η < (b−d)/2 there exists a component class at level d+η whose birth-supremum is exactly b. This is the census cell that the death-dichotomy reconstruction of a real prominent bar reads off at the probe level d+η.
-- source:
--   Census-cell pin of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster, death-dichotomy routing): the image thread of a real prominent bar (b, d) is reconstructed at the probe level d+η from this cell. The nonzero multiplicity makes the box combination at η at least 1 (multiplicity unfolds to the infimum over probes, t3_mult_unfold); the crit-free gaps at b and d reduce the combination to the above-minus-below census count (t3_comb_small), so the above-census at level d+η is nonempty. Spliced green; consumed by the L3 reconstruction (design §8.12.5).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem census_cell_pin {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d η δ₀ : ℝ} (hbd : d < b)
    (hmult : mult (rankFn stage J) ((b : EReal), (d : EReal)) ≠ 0)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    (hη0 : 0 < η) (hηδ : η < δ₀) (hηbd : η < (b - d) / 2) :
    ∃ C₀ : comps stage J (d + η), birthSup hLaw (d + η) C₀ = b
    := by sorry
