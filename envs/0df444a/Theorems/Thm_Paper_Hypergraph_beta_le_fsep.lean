-- Prove2me | Theorems.Thm_Paper_Hypergraph_beta_le_fsep
-- name    : Paper.Hypergraph.beta_le_fsep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:11.738094+00:00
-- url     : https://prove2.me/theorems/3486664b-1eea-4361-af41-d043d2063fba
-- title:
--   Hypergraph: beta le fsep
-- statement:
--   The Hypergraph construction uses the beta le fsep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1095-L1103
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1095-L1103

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.beta_le_fsep (H : Hypergraph) {W : Finset ℕ} (hW : W ⊆ H.vertices)
    {γ : ℕ → ℝ} (hγ : (H.induce W).EdgeWeight γ) {θ : ℝ} (hθ : 0 < θ ∧ θ < 1) :
    (H.induce W).beta θ γ ≤ H.fsep θ := by sorry
