-- Prove2me | Theorems.Thm_Paper_Hypergraph_cutoff_layer_parameters
-- name    : Paper.Hypergraph.cutoff_layer_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:20.505813+00:00
-- url     : https://prove2.me/theorems/8bbc32e6-6606-4b8a-9cbb-fb5edd8f74f2
-- title:
--   Hypergraph: cutoff layer parameters
-- statement:
--   The corrected number of layers fits below radius r and forces growth
--   beyond the total cover cost. The constants of Lemma 5.9 are unchanged.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L264-L316
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L264-L316

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.cutoff_layer_parameters {r K : ℝ} (hr : 0 < r) (hK : r / 2 ≤ K) :
    let L := Real.logb 2 (K / r)
    let δ := r / (9 + 2 * L)
    ∃ N : ℕ, 0 < N ∧
      r / 4 + (N : ℝ) * (3 * δ / 2) ≤ r ∧
      K < (2 : ℝ) ^ N * (5 * r / 56) ∧
      ∀ q : ℝ, q < δ / 2 → 5 * r / 56 ≤ (r / 4 - q) / 2 := by sorry
