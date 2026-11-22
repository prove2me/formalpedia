-- Prove2me | Theorems.Thm_Paper_Hypergraph_balanced_separator_rounding
-- name    : Paper.Hypergraph.balanced_separator_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:12.262441+00:00
-- url     : https://prove2.me/theorems/8ea6fd8e-09f6-4ba5-b4b4-3076236a0e24
-- title:
--   Hypergraph: balanced separator rounding
-- statement:
--   The regularized rounding bound for every fractional half-balanced separator.
--   If the empty separator is already balanced, its cover cost is zero.
--   Otherwise the supplied rounding theorem applies with `φ = 1 / 2`.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2429-L2485
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2429-L2485

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.balanced_separator_rounding (rounding : BalancedRounding) : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (H : Hypergraph) (γ x : ℕ → ℝ), H.EdgeWeight γ →
    H.FractionalBalanced γ (1 / 2) x →
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralBalanced γ (5 / 6) S ∧
      H.setCoverCost S ≤ C₀ *
        (1 + min (H.degeneracy : ℝ)
          (Real.log (2 + ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ)))) *
        (H.coverCost x + 1) * Real.log (2 + H.coverCost x) := by sorry
