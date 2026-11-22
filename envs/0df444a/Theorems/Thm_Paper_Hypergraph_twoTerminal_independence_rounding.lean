-- Prove2me | Theorems.Thm_Paper_Hypergraph_twoTerminal_independence_rounding
-- name    : Paper.Hypergraph.twoTerminal_independence_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:36.386539+00:00
-- url     : https://prove2.me/theorems/2834f0b4-06af-47f1-9527-3901222a1bcb
-- title:
--   Hypergraph: two Terminal independence rounding
-- statement:
--   The independence-number branch of Theorem 4.1.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L162-L230
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingIndependence.lean#L162-L230

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.twoTerminal_independence_rounding (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤
        (8 + 4 * Real.log ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ)) *
          H.coverCost x := by sorry
