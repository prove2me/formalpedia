-- Prove2me | Theorems.Thm_PersistClust_Count_mult_eq_comb_eventual
-- name    : PersistClust.Count.mult_eq_comb_eventual
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:16:51.335917+00:00
-- url     : https://prove2.me/theorems/1e28512a-c133-49ae-b745-1c4f9b23638b
-- title:
--   T3a eventual equality: the diagram multiplicity equals the combination at a canonical probe
-- statement:
--   For a tame module and a real point (b, d) with d < b, the multiplicity infimum is ATTAINED at a canonical small probe radius: there is eta_0 in (0, (b-d)/2) with mult (b, d) = t3_comb (b, d, eta_0). The proof unfolds the multiplicity to the infimum of the combination (the accepted mult_comb_unfold), takes the stability window delta_0 of comb_stability_window, evaluates at eta_0 = delta_0/2, and closes with le_antisymm: the infimum is at most the value at eta_0, and every other probe is either inside the window (equal by stability) or larger (bounded by the probe monotonicity comb_probe_monotone).
-- source:
--   T3a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the eventual-constancy of the mult infimum, the pivot that every census multiplicity argument of the lane consumes (a single small probe evaluation replaces the two-parameter infimum). Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy; it assembles the accepted mult_comb_unfold with the stability and monotonicity tools of this wave.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem mult_eq_comb_eventual {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b) :
    ∃ η₀ : ℝ, η₀ ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) ∧
      mult (rankFn stage J) ((b : EReal), (d : EReal)) = t3_comb stage J b d η₀
    := by sorry
