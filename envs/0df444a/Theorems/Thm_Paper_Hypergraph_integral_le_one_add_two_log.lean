-- Prove2me | Theorems.Thm_Paper_Hypergraph_integral_le_one_add_two_log
-- name    : Paper.Hypergraph.integral_le_one_add_two_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:44.734375+00:00
-- url     : https://prove2.me/theorems/e03d06df-b27f-41e2-9d60-5127947956d8
-- title:
--   Hypergraph: integral le one add two log
-- statement:
--   The integration step following Observation 4.6 for a bounded multiplier.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L19-L63
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L19-L63

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

theorem Paper.Hypergraph.integral_le_one_add_two_log {f : ℝ → ℝ} {M : ℝ}
    (hf : Measurable f) (hn : ∀ r, 0 ≤ f r) (hM : 1 ≤ M)
    (hb : ∀ r, f r ≤ M)
    (htail : ∀ t, 1 ≤ t → levelMeasure.real {r | t ≤ f r} ≤ 2 / t) :
    ∫ r, f r ∂levelMeasure ≤ 1 + 2 * Real.log M := by sorry
