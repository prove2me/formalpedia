-- Prove2me | Theorems.Thm_Paper_Hypergraph_trimDemand_support
-- name    : Paper.Hypergraph.trimDemand_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:22.233807+00:00
-- url     : https://prove2.me/theorems/235b583b-ec28-4b27-87d6-6564f56096d9
-- title:
--   Hypergraph: trim Demand support
-- statement:
--   The Hypergraph construction uses the trim Demand support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L77-L83
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L77-L83

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.trimDemand_support (H : Hypergraph) (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    H.vertices.filter (fun v => trimDemand x ε v ≠ 0) ⊆ H.vertices.filter (fun v => x v ≠ 0) := by sorry
