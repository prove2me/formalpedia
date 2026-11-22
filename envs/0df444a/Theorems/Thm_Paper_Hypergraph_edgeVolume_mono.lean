-- Prove2me | Theorems.Thm_Paper_Hypergraph_edgeVolume_mono
-- name    : Paper.Hypergraph.edgeVolume_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:27.873644+00:00
-- url     : https://prove2.me/theorems/99193c8b-a948-4834-95b6-69af423ee7c2
-- title:
--   Hypergraph: edge Volume mono
-- statement:
--   The Hypergraph construction uses the edge Volume mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L32-L40
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L32-L40

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.edgeVolume_mono (H : Hypergraph) {γ : ℕ → ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) {A B : Finset ℕ} (hAB : A ⊆ B) :
    H.edgeVolume γ A ≤ H.edgeVolume γ B := by sorry
