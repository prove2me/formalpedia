-- Prove2me | Theorems.Thm_Paper_Hypergraph_incidence_order_right_card
-- name    : Paper.Hypergraph.incidence_order_right_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:55.207593+00:00
-- url     : https://prove2.me/theorems/c103d131-fbc8-43d5-abe1-31b2cfe8db4e
-- title:
--   Hypergraph: incidence order right card
-- statement:
--   The Hypergraph construction uses the incidence order right card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L77-L89
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L77-L89

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.incidence_order_right_card (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ}
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {v : ℕ} (hv : v ∈ H.vertices) :
    (H.edges.filter (fun e => v ∈ H.edge e ∧ rank (.inl v) < rank (.inr e))).card ≤ H.degeneracy := by sorry
