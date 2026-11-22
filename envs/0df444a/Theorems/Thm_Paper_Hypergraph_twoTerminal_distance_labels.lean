-- Prove2me | Theorems.Thm_Paper_Hypergraph_twoTerminal_distance_labels
-- name    : Paper.Hypergraph.twoTerminal_distance_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:53.366314+00:00
-- url     : https://prove2.me/theorems/e7dd6104-238d-416b-a9d0-7adb460cdd22
-- title:
--   Hypergraph: two Terminal distance labels
-- statement:
--   Distances from a terminal set, without adding artificial vertices.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L88-L127
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L88-L127

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.twoTerminal_distance_labels (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ d : ℕ → ℝ,
      (∀ v ∈ H.vertices, x v ≤ d v ∧ d v ≤ 1) ∧
      (∀ v ∈ A, d v ≤ x v) ∧
      (∀ v ∈ B, 1 ≤ d v) ∧
      (∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v) := by sorry
