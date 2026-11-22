-- Prove2me | Theorems.Thm_Paper_Hypergraph_sum_incidence_swap
-- name    : Paper.Hypergraph.sum_incidence_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:43.160861+00:00
-- url     : https://prove2.me/theorems/b4b47aa1-5ed5-4dec-aa5a-7c941bb3d65e
-- title:
--   Hypergraph: sum incidence swap
-- statement:
--   The Hypergraph construction uses the sum incidence swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L415-L426
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L415-L426

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.sum_incidence_swap (H : Hypergraph) (f : ℕ → ℕ → ℝ) :
    (∑ v ∈ H.vertices, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), f v e) =
      ∑ e ∈ H.edges, ∑ v ∈ H.edge e, f v e := by sorry
