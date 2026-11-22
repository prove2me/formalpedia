-- Prove2me | Theorems.Thm_Paper_Hypergraph_cover_duality
-- name    : Paper.Hypergraph.cover_duality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:52.16992+00:00
-- url     : https://prove2.me/theorems/ed5d6987-6494-4c81-80a7-2331efb708ba
-- title:
--   Hypergraph: cover duality
-- statement:
--   The Hypergraph construction uses the cover duality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L445-L506
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L445-L506

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.cover_duality (H : Hypergraph) {x : ℕ → ℝ} (_hx : H.UnitDemand x) :
    ∃ w, H.ModularWeight w ∧ H.coverCost x = ∑ v ∈ H.vertices, w v * x v ∧
      ∀ w', H.ModularWeight w' → (∑ v ∈ H.vertices, w' v * x v) ≤ H.coverCost x := by sorry
