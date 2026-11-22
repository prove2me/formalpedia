-- Prove2me | Theorems.Thm_Paper_Hypergraph_roundingBall_volume_le
-- name    : Paper.Hypergraph.roundingBall_volume_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:06.175405+00:00
-- url     : https://prove2.me/theorems/2c5df2f8-6fd9-4c8b-b289-ac145efc3307
-- title:
--   Hypergraph: rounding Ball volume le
-- statement:
--   Observation 5.7, including balls in arbitrary induced subhypergraphs.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L77-L105
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L77-L105

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.roundingBall_volume_le (H : Hypergraph) {γ x : ℕ → ℝ} {φ r : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (Q : Finset ℕ) {c : ℕ} (hc : c ∈ H.vertices ∩ Q) (hr : r < 1) :
    H.edgeVolume γ (H.roundingBall x Q c r) ≤
      φ / (1 - r) * ∑ e ∈ H.edges, γ e := by sorry
