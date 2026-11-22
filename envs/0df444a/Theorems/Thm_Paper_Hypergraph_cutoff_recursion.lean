-- Prove2me | Theorems.Thm_Paper_Hypergraph_cutoff_recursion
-- name    : Paper.Hypergraph.cutoff_recursion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:29.769838+00:00
-- url     : https://prove2.me/theorems/db9c8af1-df31-40a2-b4de-5e06f0e33a2f
-- title:
--   Hypergraph: cutoff recursion
-- statement:
--   Repeated cut-offs terminate by deleting a nonempty piece at every step.
--   The accumulated separator has no component heavier than a single piece.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingRecursion.lean#L68-L138
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingRecursion.lean#L68-L138

import Definitions.Def_Paper_RoundingCutoff
import Definitions.Def_Paper_RoundingRecursion
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.cutoff_recursion (H : Hypergraph) {γ x : ℕ → ℝ} {V C : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hC : 0 ≤ C)
    (Q : Finset ℕ) (hQ : Q ⊆ H.vertices)
    (hcut : ∀ U ⊆ Q, U.Nonempty → Nonempty (H.CutoffPiece γ x U V C)) :
    ∃ S ⊆ Q, S ⊆ H.vertices.filter (fun v => x v ≠ 0) ∧
      (∀ K ∈ (H.induce (Q \ S)).components, H.edgeVolume γ K ≤ V) ∧
      H.setCoverCost S ≤ C * H.coverCost (restrictDemand x Q) := by sorry
