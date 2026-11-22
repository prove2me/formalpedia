-- Prove2me | Theorems.Thm_Paper_Hypergraph_indicator_balance_sum
-- name    : Paper.Hypergraph.indicator_balance_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:10.219173+00:00
-- url     : https://prove2.me/theorems/d444ae9d-0e74-4459-822f-f9c53a7235c9
-- title:
--   Hypergraph: indicator balance sum
-- statement:
--   The Hypergraph construction uses the indicator balance sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1004-L1019
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1004-L1019

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.indicator_balance_sum (H : Hypergraph) (γ : ℕ → ℝ) (S : Finset ℕ)
    {e u : ℕ} (he : e ∈ H.edges) (hue : u ∈ H.edge e)
    {K : Finset ℕ} (hK : K ∈ (H.induce (H.vertices \ S)).components) (huK : u ∈ K) :
    (∑ f ∈ H.edges, γ f * H.edgeDistance (indicator S) e f) =
      (∑ f ∈ H.edges, γ f) -
        ∑ f ∈ H.edges.filter (fun f => ¬ Disjoint (H.edge f) K), γ f := by sorry
