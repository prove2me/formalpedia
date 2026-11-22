-- Prove2me | Theorems.Thm_Paper_Hypergraph_width_hereditary
-- name    : Paper.Hypergraph.width_hereditary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:16.707063+00:00
-- url     : https://prove2.me/theorems/806fa944-4ec3-47c4-9914-9ecbe9bd12d2
-- title:
--   Hypergraph: width hereditary
-- statement:
--   The Hypergraph construction uses the width hereditary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L708-L751
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L708-L751

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.width_hereditary (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).adw ≤ H.adw ∧ (H.induce W).fhw ≤ H.fhw := by sorry
