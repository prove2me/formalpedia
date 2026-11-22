-- Prove2me | Theorems.Thm_Paper_Hypergraph_optimal_modular_le_adw
-- name    : Paper.Hypergraph.optimal_modular_le_adw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:39.298662+00:00
-- url     : https://prove2.me/theorems/c7131a16-487c-4623-bec0-0520054c2ac7
-- title:
--   Hypergraph: optimal modular le adw
-- statement:
--   The Hypergraph construction uses the optimal modular le adw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L696-L706
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L696-L706

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.optimal_modular_le_adw (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w) :
    H.optimalWidth (modularValue w) ≤ H.adw := by sorry
