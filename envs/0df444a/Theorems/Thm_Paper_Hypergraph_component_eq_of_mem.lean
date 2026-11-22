-- Prove2me | Theorems.Thm_Paper_Hypergraph_component_eq_of_mem
-- name    : Paper.Hypergraph.component_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:43.910209+00:00
-- url     : https://prove2.me/theorems/225c3dc1-0976-4d15-805d-a6b5856508bf
-- title:
--   Hypergraph: component eq of mem
-- statement:
--   Components that share a vertex are equal.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1314-L1322
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1314-L1322

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.component_eq_of_mem (H : Hypergraph) {C K : Finset ℕ}
    (hC : C ∈ H.components) (hK : K ∈ H.components) {v : ℕ}
    (hvC : v ∈ C) (hvK : v ∈ K) : C = K := by sorry
