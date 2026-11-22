-- Prove2me | Theorems.Thm_Paper_Hypergraph_optimal_submodular_le_fhw
-- name    : Paper.Hypergraph.optimal_submodular_le_fhw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:55.0278+00:00
-- url     : https://prove2.me/theorems/25c57b49-73a0-4f1e-90c8-c079c8ddab69
-- title:
--   Hypergraph: optimal submodular le fhw
-- statement:
--   The Hypergraph construction uses the optimal submodular le fhw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L537-L549
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L537-L549

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.optimal_submodular_le_fhw (H : Hypergraph) {b : Finset ℕ → ℝ}
    (hb : H.SubmodularWeight b) : H.optimalWidth b ≤ H.fhw := by sorry
