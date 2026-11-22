-- Prove2me | Theorems.Thm_Paper_Hypergraph_vertexDistance_indicator
-- name    : Paper.Hypergraph.vertexDistance_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:05.074193+00:00
-- url     : https://prove2.me/theorems/aff284ae-4251-4b68-bb9e-298af6de8453
-- title:
--   Hypergraph: vertex Distance indicator
-- statement:
--   The Hypergraph construction uses the vertex Distance indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L821-L866
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L821-L866

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.vertexDistance_indicator (H : Hypergraph) (S : Finset ℕ) {u v : ℕ}
    (hu : u ∈ H.vertices) (_hv : v ∈ H.vertices) :
    H.vertexDistance (indicator S) u v =
      if u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v
      then 0 else 1 := by sorry
