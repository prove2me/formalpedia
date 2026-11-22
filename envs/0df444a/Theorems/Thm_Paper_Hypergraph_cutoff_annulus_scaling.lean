-- Prove2me | Theorems.Thm_Paper_Hypergraph_cutoff_annulus_scaling
-- name    : Paper.Hypergraph.cutoff_annulus_scaling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:51.908801+00:00
-- url     : https://prove2.me/theorems/6dbc0233-02d3-4f8a-b637-1627501cf009
-- title:
--   Hypergraph: cutoff annulus scaling
-- statement:
--   The corrected annuli give unit demands and the original scaling factor.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L319-L333
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L319-L333

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.cutoff_annulus_scaling {r L q : ℝ} (hr : 0 < r)
    (hD : 0 < 9 + 2 * L) (hq : q < (r / (9 + 2 * L)) / 2) :
    let δ := r / (9 + 2 * L)
    0 < δ - q ∧
      1 / (δ - q) ≤ (18 + 4 * L) / r ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ q → 0 ≤ u / (δ - q) ∧ u / (δ - q) < 1 := by sorry
