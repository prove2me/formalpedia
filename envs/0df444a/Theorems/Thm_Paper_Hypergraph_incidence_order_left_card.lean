-- Prove2me | Theorems.Thm_Paper_Hypergraph_incidence_order_left_card
-- name    : Paper.Hypergraph.incidence_order_left_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:51.167128+00:00
-- url     : https://prove2.me/theorems/fd5620c8-309c-4b37-9e21-f9a478294e0e
-- title:
--   Hypergraph: incidence order left card
-- statement:
--   The Hypergraph construction uses the incidence order left card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L63-L75
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingDegeneracy.lean#L63-L75

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.incidence_order_left_card (H : Hypergraph) {rank : ℕ ⊕ ℕ → ℕ}
    (hlater : ∀ v ∈ H.incidenceVertices,
      (H.incidenceVertices.filter (fun w => H.incidence.Adj v w ∧ rank v < rank w)).card ≤ H.degeneracy)
    {e : ℕ} (he : e ∈ H.edges) :
    ((H.edge e).filter (fun v => rank (.inr e) < rank (.inl v))).card ≤ H.degeneracy := by sorry
