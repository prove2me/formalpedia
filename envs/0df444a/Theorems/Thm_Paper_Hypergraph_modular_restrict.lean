-- Prove2me | Theorems.Thm_Paper_Hypergraph_modular_restrict
-- name    : Paper.Hypergraph.modular_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:52.635153+00:00
-- url     : https://prove2.me/theorems/da22d276-5366-48d0-892d-ac810adeebc0
-- title:
--   Hypergraph: modular restrict
-- statement:
--   The Hypergraph construction uses the modular restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2282-L2293
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2282-L2293

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.modular_restrict (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w) :
    (fun v => if v ∈ H.vertices then w v else 0) ∈ H.modularCube := by sorry
