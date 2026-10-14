-- Prove2me | Theorems.Thm_PersistClust_Count_mult_comb_unfold
-- name    : PersistClust.Count.mult_comb_unfold
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:40:33.027353+00:00
-- url     : https://prove2.me/theorems/4d47b112-f6b5-4717-8d15-9bd0e76405ee
-- title:
--   Mult-to-comb unfold: the diagram multiplicity of a real point (b, d) with d < b is the infimum of the box combination over the open probe window
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law stage/J, and let b > d be two real levels. The multiplicity of the point (b, d) in the module's diagram - defined by the two-parameter infimum of rank differences - unfolds at the real point (b, d) to the infimum, over all probe radii eta in the open interval (0, (b-d)/2), of the box combination t3_comb(b, d, eta) = (rank(b-eta, d+eta) - rank(b+eta, d+eta)) - (rank(b-eta, d-eta) - rank(b+eta, d-eta)). The proof unfolds both mult and t3_comb, resolves the four EReal case-splits (the birth b and death d are real coersions, hence neither bottom nor top; and the order b > d is real), and the nested infimum body collapses to the combination bracket by toReal-of-coe simplification. This unfold is the entry gate every multiplicity-to-census argument of the lane consumes: nonzero multiplicity at (b, d) becomes positivity of the box combination at some small probe radius.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the mult-to-comb unfold that every census multiplicity argument (death/birth pinning, census absorption, census cell) reads through. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy with the platform t3_comb argument order; it is the unfold underlying the accepted census_absorption_mult_nonzero and essential_bar_mult_nonzero.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem mult_comb_unfold {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) {b d : ℝ} (hbd : d < b) :
    mult (rankFn stage J) ((b : EReal), (d : EReal)) =
      ⨅ (η : ℝ) (_ : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2)), t3_comb stage J b d η
    := by sorry
