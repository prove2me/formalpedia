-- Prove2me | Theorems.Thm_Paper_Hypergraph_vertexDistance_congr_on_vertices
-- name    : Paper.Hypergraph.vertexDistance_congr_on_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:13.310271+00:00
-- url     : https://prove2.me/theorems/36edb238-9003-4c5f-8f23-6514930a6959
-- title:
--   Hypergraph: vertex Distance congr on vertices
-- statement:
--   The Hypergraph construction uses the vertex Distance congr on vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L83-L88
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L83-L88

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.vertexDistance_congr_on_vertices (H : Hypergraph) {x y : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (hxy : ∀ v ∈ H.vertices, x v = y v)
    {u v : ℕ} (hu : u ∈ H.vertices) : H.vertexDistance x u v = H.vertexDistance y u v := by sorry
