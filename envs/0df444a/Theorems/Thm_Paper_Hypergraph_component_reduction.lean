-- Prove2me | Theorems.Thm_Paper_Hypergraph_component_reduction
-- name    : Paper.Hypergraph.component_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:51.917612+00:00
-- url     : https://prove2.me/theorems/6e2400c3-0aa9-4f30-a10f-a4a99f565906
-- title:
--   Hypergraph: component reduction
-- statement:
--   The Hypergraph construction uses the component reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1416-L1460
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1416-L1460

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.component_reduction (H : Hypergraph) :
    H.fhw = sSup (insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).fhw}) ∧
    H.adw = sSup (insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).adw}) := by sorry
