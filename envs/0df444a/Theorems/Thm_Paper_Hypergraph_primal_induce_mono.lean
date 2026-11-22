-- Prove2me | Theorems.Thm_Paper_Hypergraph_primal_induce_mono
-- name    : Paper.Hypergraph.primal_induce_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:56.154605+00:00
-- url     : https://prove2.me/theorems/0a4ce15d-04de-4b0b-ac2f-d5a80960820f
-- title:
--   Hypergraph: primal induce mono
-- statement:
--   The Hypergraph construction uses the primal induce mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1572-L1578
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1572-L1578

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.primal_induce_mono (H : Hypergraph) {U W : Finset ℕ} (hUW : U ⊆ W) :
    (H.induce U).primal ≤ (H.induce W).primal := by sorry
