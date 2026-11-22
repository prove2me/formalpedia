-- Prove2me | Theorems.Thm_Paper_Hypergraph_primal_induce_le
-- name    : Paper.Hypergraph.primal_induce_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:19.516837+00:00
-- url     : https://prove2.me/theorems/471c40aa-5273-476d-820f-cf2d270d9279
-- title:
--   Hypergraph: primal induce le
-- statement:
--   The Hypergraph construction uses the primal induce le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L816-L819
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L816-L819

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.primal_induce_le (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).primal ≤ H.primal := by sorry
