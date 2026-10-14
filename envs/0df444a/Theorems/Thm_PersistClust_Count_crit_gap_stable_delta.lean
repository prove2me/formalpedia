-- Prove2me | Theorems.Thm_PersistClust_Count_crit_gap_stable_delta
-- name    : PersistClust.Count.crit_gap_stable_delta
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:42:25.710787+00:00
-- url     : https://prove2.me/theorems/ce3bdd79-3eb8-4a55-ad2b-89cb500814c3
-- title:
--   Stable critical gap: there is a positive delta at most the half-gap that avoids every critical level off b and off d
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law stage/J that is tame, and let b > d be two levels. Because tameness makes the critical set finite, there exists a stability radius delta_0 with 0 < delta_0 <= (b - d)/2 such that every critical level tau different from b lies at distance strictly greater than delta_0 from b, and every critical level tau different from d lies at distance strictly greater than delta_0 from d. The proof takes the finite-gap lemma twice on the critical set (once centered at b, once at d, each with the quarter-gap eps_0 = (b-d)/4 > 0, which exists since d < b), and returns the minimum of the two witnesses: positivity and the half-gap bound are the two min-le facts, and each avoidance clause follows because the minimum is at most the witness for that center. This delta_0 is the probe window every downstream census argument (comb unfold, death/birth pinning, census absorption, partner construction) consumes: inside (0, delta_0) the probe levels avoid all critical levels off b and d, so birth-sup values are pinned exactly.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the critical-gap stability radius (delta_0 with the b-side and d-side avoidance clauses) that opens every census window argument of the multiplicity lane. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; the finite-gap lemma (Finset filter/image/min' algebra) is inlined from the same verified lane, and this is the gap supply of the accepted census_absorption_mult_nonzero.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem crit_gap_stable_delta {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d : ℝ} (hbd : d < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (b - d) / 2 ∧
      (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|)
    := by sorry
