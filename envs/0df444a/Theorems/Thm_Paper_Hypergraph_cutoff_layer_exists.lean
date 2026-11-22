-- Prove2me | Theorems.Thm_Paper_Hypergraph_cutoff_layer_exists
-- name    : Paper.Hypergraph.cutoff_layer_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:43.64227+00:00
-- url     : https://prove2.me/theorems/ed56f9a7-1e96-4f93-bb3e-0f09e9c134f7
-- title:
--   Hypergraph: cutoff layer exists
-- statement:
--   A finite growth argument for the corrected cut-off construction.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L241-L260
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L241-L260

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.cutoff_layer_exists (a ℓ : ℕ → ℝ) (N : ℕ) {b K : ℝ}
    (hseed : b ≤ a 0) (hbudget : K < 2 ^ N * b) (hupper : a N ≤ K)
    (hadd : ∀ i < N, a i + ℓ i ≤ a (i + 1)) :
    ∃ i < N, ℓ i ≤ a i := by sorry
