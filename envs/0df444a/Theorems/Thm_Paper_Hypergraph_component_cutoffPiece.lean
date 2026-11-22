-- Prove2me | Theorems.Thm_Paper_Hypergraph_component_cutoffPiece
-- name    : Paper.Hypergraph.component_cutoffPiece
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:25.430655+00:00
-- url     : https://prove2.me/theorems/8d4abad9-ca40-4724-a691-ade23d2d87d5
-- title:
--   Hypergraph: component cutoff Piece
-- statement:
--   The Hypergraph construction uses the component cutoff Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean#L84-L123
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean#L84-L123

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_RoundingCutoff
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.component_cutoffPiece (H : Hypergraph) {γ x : ℕ → ℝ} {φ r C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (hr : r < 1) (hC : 0 ≤ C) {Q : Finset ℕ} (hQ : Q ⊆ H.vertices)
    {c : ℕ} (hc : c ∈ Q)
    (hball : ∀ v, (H.induce Q).primal.Reachable c v → (H.induce Q).vertexDistance x c v ≤ r) :
    Nonempty (H.CutoffPiece γ x Q (φ / (1 - r) * ∑ e ∈ H.edges, γ e) C) := by sorry
