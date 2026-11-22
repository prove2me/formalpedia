-- Prove2me | Theorems.Thm_Paper_Hypergraph_primal_induce_adj
-- name    : Paper.Hypergraph.primal_induce_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:05.259519+00:00
-- url     : https://prove2.me/theorems/546a1586-b298-45c2-a4de-ee319ec21604
-- title:
--   Hypergraph: primal induce adj
-- statement:
--   The Hypergraph construction uses the primal induce adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L661-L669
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L661-L669

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.primal_induce_adj (H : Hypergraph) (W : Finset ℕ) {u v : ℕ}
    (hu : u ∈ W) (hv : v ∈ W) :
    (H.induce W).primal.Adj u v ↔ H.primal.Adj u v := by sorry
