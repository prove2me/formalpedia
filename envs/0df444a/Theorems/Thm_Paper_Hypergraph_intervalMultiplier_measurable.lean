-- Prove2me | Theorems.Thm_Paper_Hypergraph_intervalMultiplier_measurable
-- name    : Paper.Hypergraph.intervalMultiplier_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:50.939458+00:00
-- url     : https://prove2.me/theorems/8bc43b58-809c-49b2-bc5f-316e8719ada0
-- title:
--   Hypergraph: interval Multiplier measurable
-- statement:
--   The Hypergraph construction uses the interval Multiplier measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L74-L78
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L74-L78

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

theorem Paper.Hypergraph.intervalMultiplier_measurable (V : Finset ℕ) (hne : V.Nonempty) (x d : ℕ → ℝ) :
    Measurable (intervalMultiplier V hne x d) := by sorry
