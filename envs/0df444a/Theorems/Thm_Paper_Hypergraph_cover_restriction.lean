-- Prove2me | Theorems.Thm_Paper_Hypergraph_cover_restriction
-- name    : Paper.Hypergraph.cover_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:39.029803+00:00
-- url     : https://prove2.me/theorems/f179e48e-493a-4cc0-a5af-e05d234b62e6
-- title:
--   Hypergraph: cover restriction
-- statement:
--   The Hypergraph construction uses the cover restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L213-L256
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L213-L256

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.cover_restriction (H : Hypergraph) {X W : Finset ℕ}
    (hXW : X ⊆ W) :
    (H.induce W).setCoverCost X = H.setCoverCost X := by sorry
