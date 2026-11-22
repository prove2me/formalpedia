-- Prove2me | Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
-- name    : Paper.Hypergraph.component_mem_iff_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:12.542915+00:00
-- url     : https://prove2.me/theorems/9234e6ed-c95c-4f66-b296-4edb8e2d07d7
-- title:
--   Hypergraph: component mem iff reachable
-- statement:
--   The Hypergraph construction uses the component mem iff reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L951-L961
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L951-L961

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.component_mem_iff_reachable (H : Hypergraph) {K : Finset ℕ}
    (hK : K ∈ H.components) {u v : ℕ} (hu : u ∈ K) (hv : v ∈ H.vertices) :
    v ∈ K ↔ H.primal.Reachable u v := by sorry
