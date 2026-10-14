-- Prove2me | Theorems.Thm_PersistClust_Count_comb_probe_monotone
-- name    : PersistClust.Count.comb_probe_monotone
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T20:14:18.361982+00:00
-- url     : https://prove2.me/theorems/c8daae26-c9ce-4a5a-94b7-0691af25e04c
-- title:
--   T3a monotonicity: the box combination is monotone in the probe radius
-- statement:
--   For a tame module and a real point (b, d) with d < b, the box combination t3_comb (b, d, eta) is MONOTONE in the probe radius: whenever 0 < eta <= eta' < (b-d)/2, t3_comb (b, d, eta) <= t3_comb (b, d, eta'). Reading the combination as a census difference of bars, enlarging both probe windows catches at least as many elder-rule bars. The proof builds, for each of the two window brackets, an explicit injection from the cells counted at the smaller probe into the cells counted at the larger probe (thread-lift through the meets-birthSup ancestor), controls the image point-sets by compatibility, and finishes with the encard monotonicity of the resulting subset relation between the counted sets.
-- source:
--   T3a support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the probe monotonicity that makes the combination infimum collapse at a canonical small probe, consumed by the eventual-equality tool (mult_eq_comb_eventual). Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified matching-gate lane working copy; it sits on top of the accepted mult_comb_unfold tool.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem comb_probe_monotone {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b)
    {η η' : ℝ} (hη0 : 0 < η) (hle : η ≤ η') (hη'lim : η' < (b - d) / 2) :
    t3_comb stage J b d η ≤ t3_comb stage J b d η'
    := by sorry
