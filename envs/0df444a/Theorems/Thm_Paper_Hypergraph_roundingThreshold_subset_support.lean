-- Prove2me | Theorems.Thm_Paper_Hypergraph_roundingThreshold_subset_support
-- name    : Paper.Hypergraph.roundingThreshold_subset_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:35.782098+00:00
-- url     : https://prove2.me/theorems/e43a8437-25c4-4048-af08-d50cb20f21ff
-- title:
--   Hypergraph: rounding Threshold subset support
-- statement:
--   The Hypergraph construction uses the rounding Threshold subset support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L111-L116
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L111-L116

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.roundingThreshold_subset_support (H : Hypergraph) (x : ℕ → ℝ)
    {a : ℝ} (ha : 0 < a) :
    H.roundingThreshold x a ⊆ H.vertices.filter (fun v => x v ≠ 0) := by sorry
