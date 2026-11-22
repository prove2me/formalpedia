-- Prove2me | Theorems.Thm_Paper_Hypergraph_cutoff_from_rounding
-- name    : Paper.Hypergraph.cutoff_from_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:34.78951+00:00
-- url     : https://prove2.me/theorems/d7ba4ff4-6770-4827-a239-f018f38e162d
-- title:
--   Hypergraph: cutoff from rounding
-- statement:
--   The graph-theoretic cut-off construction from a two-terminal rounding rule.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean#L126-L285
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean#L126-L285

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_RoundingCutoff
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.cutoff_from_rounding (H : Hypergraph) {γ x : ℕ → ℝ} {φ r C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (hr : 0 < r ∧ r < 1) (hC : 0 ≤ C) (hK : r / 2 ≤ H.coverCost x)
    {Q : Finset ℕ} (hQ : Q ⊆ H.vertices) (hne : Q.Nonempty)
    (hsmall : ∀ v ∈ Q, x v < (r / (9 + 2 * Real.logb 2 (H.coverCost x / r))) / 2)
    (hround : ∀ (A B : Finset ℕ) (z : ℕ → ℝ),
      A ⊆ (H.induce Q).vertices → B ⊆ (H.induce Q).vertices →
      (H.induce Q).FractionalSeparator A B z →
      (∀ v ∈ (H.induce Q).vertices, z v ≠ 0 → x v ≠ 0) →
      ∃ S ⊆ (H.induce Q).vertices.filter (fun v => z v ≠ 0),
        (H.induce Q).IntegralSeparator A B S ∧
        H.setCoverCost S ≤ C * (H.induce Q).coverCost z) :
    Nonempty (H.CutoffPiece γ x Q (φ / (1 - r) * ∑ e ∈ H.edges, γ e)
      (C * ((18 + 4 * Real.logb 2 (H.coverCost x / r)) / r))) := by sorry
