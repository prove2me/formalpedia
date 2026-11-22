-- Prove2me | Theorems.Thm_Paper_Hypergraph_modularValue_submodular
-- name    : Paper.Hypergraph.modularValue_submodular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:26.547734+00:00
-- url     : https://prove2.me/theorems/da95be62-dbef-4121-b938-0534d5c57fdb
-- title:
--   Hypergraph: modular Value submodular
-- statement:
--   The Hypergraph construction uses the modular Value submodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L195-L201
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L195-L201

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.modularValue_submodular (H : Hypergraph) {w : ℕ → ℝ}
    (hw : H.ModularWeight w) : H.SubmodularWeight (modularValue w) := by sorry
