-- Prove2me | Theorems.Thm_Paper_Hypergraph_rounding_by_average
-- name    : Paper.Hypergraph.rounding_by_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:21.340986+00:00
-- url     : https://prove2.me/theorems/50236d8e-843c-4e5d-bf09-7a3b87e57f2c
-- title:
--   Hypergraph: rounding by average
-- statement:
--   Select an interior level whose cover cost is at most its expectation.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L150-L165
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L150-L165

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.rounding_by_average (H : Hypergraph) {A B : Finset ℕ} {x d : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices)
    (ha : ∀ v ∈ A, d v ≤ x v) (hb : ∀ v ∈ B, 1 ≤ d v)
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    (m : ℕ → ℝ → ℝ) (hi : ∀ e ∈ H.edges, Integrable (m e) levelMeasure)
    (hc : ∀ r ∈ Ioo 0 1, H.Cover (indicator (H.levelSeparator x d r)) (fun e => m e r)) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ ∑ e ∈ H.edges, ∫ r, m e r ∂levelMeasure := by sorry
