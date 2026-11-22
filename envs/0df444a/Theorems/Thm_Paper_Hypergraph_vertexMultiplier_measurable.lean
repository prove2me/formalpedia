-- Prove2me | Theorems.Thm_Paper_Hypergraph_vertexMultiplier_measurable
-- name    : Paper.Hypergraph.vertexMultiplier_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:51.506647+00:00
-- url     : https://prove2.me/theorems/e9674350-d5e9-49e6-b0df-de68f29321f4
-- title:
--   Hypergraph: vertex Multiplier measurable
-- statement:
--   The Hypergraph construction uses the vertex Multiplier measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L71-L72
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingAveraging.lean#L71-L72

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

theorem Paper.Hypergraph.vertexMultiplier_measurable (x d : ℕ → ℝ) (v : ℕ) :
    Measurable (vertexMultiplier x d v) := by sorry
