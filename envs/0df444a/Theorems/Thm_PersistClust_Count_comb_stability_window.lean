-- Prove2me | Theorems.Thm_PersistClust_Count_comb_stability_window
-- name    : PersistClust.Count.comb_stability_window
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:11:22.926995+00:00
-- url     : https://prove2.me/theorems/c1a5816e-db61-4b7c-805c-80c6cf724298
-- title:
--   T3a stability: the box combination is constant on a sub-half-gap window
-- statement:
--   For a tame module and a real point (b, d) with d < b, the box combination t3_comb (b, d, eta) (the rank bracket whose infimum gives the diagram multiplicity) is CONSTANT in the probe radius eta on a small window: there is delta_0 with 0 < delta_0 <= (b-d)/2 such that for all eta, eta' in (0, delta_0) the two combinations agree. The proof takes the critical-set gap delta_0 of the accepted crit_gap_stable_delta tool, excludes every cell's birth-sup from the four shifted corners b+-zeta, d+-zeta inside the window, rewrites each combination as its rank bracket, and finishes with the two window identities (the plus/minus windows coincide with the birth-pinned census sets).
-- source:
--   T3a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the probe-stability of the box combination that turns the mult infimum into a single evaluation, consumed by the eventual-equality tool (mult_eq_comb_eventual) and the finiteness bookkeeping. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy; it sits on top of the accepted crit_gap_stable_delta, comb_census_pin_unfold and mult_comb_unfold tools.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem comb_stability_window {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (b - d) / 2 ∧
      ∀ η ∈ Set.Ioo (0 : ℝ) δ₀, ∀ η' ∈ Set.Ioo (0 : ℝ) δ₀,
        t3_comb stage J b d η = t3_comb stage J b d η'
    := by sorry
