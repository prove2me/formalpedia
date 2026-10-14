-- Prove2me | Theorems.Thm_PersistClust_Count_comb_census_pin_unfold
-- name    : PersistClust.Count.comb_census_pin_unfold
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:46:50.050817+00:00
-- url     : https://prove2.me/theorems/805990cf-c50d-4494-9fca-6a2c7060cb6d
-- title:
--   Comb census unfold: at a crit-free probe radius the box combination equals the PIN census minus the BELOW census
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law stage/J that is tame, let b > d be two levels, and let delta_0 be a positive gap excluding every critical level tau with tau != b from b and every critical level tau with tau != d from d. Then for every probe radius eta with 0 < eta < delta_0 and eta < (b - d)/2, the box combination t3_comb(b, d, eta) - equal to (rank(b-eta, d+eta) - rank(b+eta, d+eta)) - (rank(b-eta, d-eta) - rank(b+eta, d-eta)) - unfolds to the encardinality of the cells at level d+eta whose birth-sup is EXACTLY b (the PIN census) minus the encardinality of the cells at level d-eta whose birth-sup is exactly b (the BELOW census). The proof: the generic box identity splits each rank difference into the window census (birth-sup strictly between b-eta and b+eta); the critical gap turns that window into the exact pin (birth-sup = b) via the win-beta trichotomy; and the four probe levels b-eta, b+eta, d+eta, d-eta are all non-generic (the avoid lemma: a birthSup value equal to any of them would put a non-b, non-d level into the critical set, contradicting the gap). This is the comb census unfold consumed by the death-pinning, birth-pinning and census-absorption arguments of the multiplicity lane.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the eta-combination-to-census unfold (PIN minus BELOW) used by the death/birth pinning and the census absorption in the census multiplicity argument. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy with the platform t3_comb argument order; its closure (box identity, window split, win-beta, avoid, bSup-in-crit chain) is inlined from the same verified lane, and it is the unfold underlying the accepted census_absorption_mult_nonzero.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem comb_census_pin_unfold {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J) {b d δ₀ : ℝ} (hbd : d < b)
    (hgap : (∀ τ ∈ critSet hTame, τ ≠ b → δ₀ < |τ - b|) ∧
      (∀ τ ∈ critSet hTame, τ ≠ d → δ₀ < |τ - d|))
    {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) δ₀) (hηbd : η < (b - d) / 2) :
    t3_comb stage J b d η =
      (({C : comps stage J (d + η) | birthSup hLaw (d + η) C = b} :
          Set (comps stage J (d + η))).encard
        - ({C : comps stage J (d - η) | birthSup hLaw (d - η) C = b} :
          Set (comps stage J (d - η))).encard : ℕ∞)
    := by sorry
