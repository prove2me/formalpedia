-- Prove2me | Theorems.Thm_Paper_Hypergraph_nontrivial_rounding_cover_lower_bound
-- name    : Paper.Hypergraph.nontrivial_rounding_cover_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:35.869345+00:00
-- url     : https://prove2.me/theorems/6113aa54-2ad6-452d-b3e1-8472f331b7cb
-- title:
--   Hypergraph: nontrivial rounding cover lower bound
-- statement:
--   The nontrivial branch has enough cover cost for the logarithmic layer budget.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/BalancedRounding.lean#L25-L50
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/BalancedRounding.lean#L25-L50

import Definitions.Def_Paper_RoundingRecursion
import Definitions.Def_Paper_TwoTerminalRounding
import Definitions.Def_Paper_BalancedRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.nontrivial_rounding_cover_lower_bound (H : Hypergraph) {γ x : ℕ → ℝ} {φ : ℝ}
    (hφ : 0 < φ ∧ φ < 1) (hγ : ∀ e ∈ H.edges, 0 ≤ γ e)
    (hx : H.FractionalBalanced γ φ x)
    (hnontrivial : ¬ H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) ∅) :
    (1 - φ) / 4 ≤ H.coverCost x := by sorry
