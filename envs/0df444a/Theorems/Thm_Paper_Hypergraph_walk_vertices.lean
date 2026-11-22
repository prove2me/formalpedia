-- Prove2me | Theorems.Thm_Paper_Hypergraph_walk_vertices
-- name    : Paper.Hypergraph.walk_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:06.219685+00:00
-- url     : https://prove2.me/theorems/f6eb70ce-5f6e-4db8-bd5b-57060f4a016b
-- title:
--   Hypergraph: walk vertices
-- statement:
--   A walk starting in the hypergraph never visits the unused ambient vertices.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L793-L803
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L793-L803

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.walk_vertices (H : Hypergraph) {u v : ℕ} (p : H.primal.Walk u v)
    (hu : u ∈ H.vertices) : ∀ z ∈ p.support, z ∈ H.vertices := by sorry
