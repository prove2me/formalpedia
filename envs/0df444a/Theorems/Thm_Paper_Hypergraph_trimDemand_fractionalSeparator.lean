-- Prove2me | Theorems.Thm_Paper_Hypergraph_trimDemand_fractionalSeparator
-- name    : Paper.Hypergraph.trimDemand_fractionalSeparator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:33.2498+00:00
-- url     : https://prove2.me/theorems/212a21dd-2ade-47e5-b035-ea116eb906ac
-- title:
--   Hypergraph: trim Demand fractional Separator
-- statement:
--   Removing small demands loses at most half the weight of a shortest path.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L97-L159
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L97-L159

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.trimDemand_fractionalSeparator (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) {ε : ℝ} (hε : 0 < ε)
    (hbudget : ε * (2 * (H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ) ≤ 1 / 2) :
    H.FractionalSeparator A B (trimDemand x ε) := by sorry
