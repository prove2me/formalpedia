-- Prove2me | Theorems.Thm_Paper_Hypergraph_edgeDistance_indicator
-- name    : Paper.Hypergraph.edgeDistance_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:23.870577+00:00
-- url     : https://prove2.me/theorems/a64585e6-0900-43a5-9591-3abe661f1d97
-- title:
--   Hypergraph: edge Distance indicator
-- statement:
--   The Hypergraph construction uses the edge Distance indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L868-L898
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L868-L898

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.edgeDistance_indicator (H : Hypergraph) (S : Finset ℕ) {e f : ℕ}
    (he : e ∈ H.edges) (hf : f ∈ H.edges) :
    H.edgeDistance (indicator S) e f =
      if ∃ u ∈ H.edge e, ∃ v ∈ H.edge f,
        u ∉ S ∧ v ∉ S ∧ (H.induce (H.vertices \ S)).primal.Reachable u v
      then 0 else 1 := by sorry
