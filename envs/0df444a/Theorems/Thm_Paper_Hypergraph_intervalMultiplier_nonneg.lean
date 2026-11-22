-- Prove2me | Theorems.Thm_Paper_Hypergraph_intervalMultiplier_nonneg
-- name    : Paper.Hypergraph.intervalMultiplier_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:05.004805+00:00
-- url     : https://prove2.me/theorems/9e1fedcc-e4b6-4675-897d-7d6d49337c59
-- title:
--   Hypergraph: interval Multiplier nonneg
-- statement:
--   The Hypergraph construction uses the interval Multiplier nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L84-L89
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L84-L89

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

theorem Paper.Hypergraph.intervalMultiplier_nonneg {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ}
    (hx : ∀ v ∈ V, 0 ≤ x v) (r : ℝ) : 0 ≤ intervalMultiplier V hne x d r := by sorry
