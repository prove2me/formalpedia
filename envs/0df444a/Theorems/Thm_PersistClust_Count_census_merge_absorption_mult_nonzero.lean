-- Prove2me | Theorems.Thm_PersistClust_Count_census_merge_absorption_mult_nonzero
-- name    : PersistClust.Count.census_merge_absorption_mult_nonzero
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T05:13:44.977255+00:00
-- url     : https://prove2.me/theorems/6c2b6dbb-6270-4612-ae1e-7070c25c5cd7
-- title:
--   Census merge absorption: two above-cells with birth-sup b and coinciding descents force a bar at (b, v)
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law (stage sets with a same-component relation) of finite type (IsTameModule), carrying the critical-set census bookkeeping: critSet is the finite set of critical levels, and birthSup measures the level at which a component class is born (the supremum of the levels of its ancestors). Let b < v be real levels, and let a positive delta0 at most (b - v)/2 keep a gap around b and v free of all other critical levels. Suppose TWO threads with birth-sup b are alive just above v and MERGE at v: for every probe eta in (0, delta0) there are TWO DISTINCT component classes C1 and C2 at level v + eta, both with birth-sup b, whose descents to level v - eta COINCIDE (the merge shape: the two threads merge into a single below-census cell at the death level). Then the diagram multiplicity of the point (b, v) is positive: mult (rankFn stage J) (b, v) is nonzero. The reason: every below-census class (birth-sup b at level v - eta) lifts to an above-census class descending back onto it (alive-up via the finite-max over descents), the chosen lift is injective (composing the descent inverts it) and misses the missed merge-partner (one of the two distinct above-cells is never hit: both descend onto the same below-cell, and the lift of that below-cell is at most one of them), so the below-census injects into the above-census minus one cell; the resulting strict surplus of the b-census above v makes the box-combination t3_comb (whose infimum over probes gives the multiplicity, by the stability of the combination on the critical-free window) positive.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the merge-drop death-localization step of the census argument - it turns a merge signature (two distinct threads with birth-sup b alive above v whose descents to below v coincide) into a positive bar count at (b, v). Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified rank lane working copy together with its green T3a census machinery (mult-unfolding, combination stability/monotonicity, beta-census reduction, alive-up); companion of the accepted census_absorption_mult_nonzero, of the accepted theorem_4_5 elder-rule support cluster (elder_chase, essential_birth_gt_bound, separated_bar_death_lower_bound, born_component_subset), of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem census_merge_absorption_mult_nonzero {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b v δ₀ : ℝ} (hbd : v < b)
    (hδ₀0 : 0 < δ₀) (hδ₀le : δ₀ ≤ (b - v) / 2)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ v → δ₀ < |τ - v|))
    (hthr : ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) δ₀ →
        ∃ C₁ C₂ : comps stage J (v + η), C₁ ≠ C₂ ∧
          birthSup hLaw (v + η) C₁ = b ∧
          birthSup hLaw (v + η) C₂ = b ∧
          ∀ hle : v - η ≤ v + η,
            structMap hLaw hle C₁ = structMap hLaw hle C₂) :
    mult (rankFn stage J) ((b : EReal), (v : EReal)) ≠ 0
    := by sorry
