-- Prove2me | Theorems.Thm_PersistClust_Count_gap_excess
-- name    : PersistClust.Count.gap_excess
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T15:17:00.115976+00:00
-- url     : https://prove2.me/theorems/e3ac75c2-8103-4c4f-93bc-d3ab9ebdaf43
-- title:
--   Positive gap bounded by ε₀ avoiding a finite set away from a point
-- statement:
--   For every finite set F of reals, every ε₀ > 0 and every point p, there exists a δ₀ with 0 < δ₀ and δ₀ ≤ ε₀ such that δ₀ < |τ - p| for every τ ∈ F with τ ≠ p: the distances from p to the elements of F other than p have a positive minimum, and halving the minimum of ε₀ with that distance keeps the gap positive, at most ε₀, and strictly below every nonzero distance to the set.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the critSet gap-excess window lemma (T3-gap) of the comb family — the isolation margin used to keep the finitely many critical levels a positive distance away from the chosen parameters b, d when cutting crit-free windows in the rank-level kill (rankR1).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem gap_excess {ε₀ : ℝ} (F : Finset ℝ) (hε : 0 < ε₀) (p : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ ε₀ ∧ ∀ τ ∈ F, τ ≠ p → δ₀ < |τ - p|
    := by sorry
