-- Prove2me | Theorems.Thm_Paper_Hypergraph_concave_finiteEdgeDistance
-- name    : Paper.Hypergraph.concave_finiteEdgeDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:29.861092+00:00
-- url     : https://prove2.me/theorems/90b3ede6-5408-4e0f-b073-fe0d4ea93210
-- title:
--   Hypergraph: concave finite Edge Distance
-- statement:
--   The Hypergraph construction uses the concave finite Edge Distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2161-L2176
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2161-L2176

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.concave_finiteEdgeDistance (H : Hypergraph) (e f : ℕ) :
    ConcaveOn ℝ Set.univ (H.finiteEdgeDistance e f) := by sorry
