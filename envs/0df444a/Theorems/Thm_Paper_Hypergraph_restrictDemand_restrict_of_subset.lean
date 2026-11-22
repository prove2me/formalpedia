-- Prove2me | Theorems.Thm_Paper_Hypergraph_restrictDemand_restrict_of_subset
-- name    : Paper.Hypergraph.restrictDemand_restrict_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:50.593887+00:00
-- url     : https://prove2.me/theorems/622d8348-e898-4c55-b30b-f8c72b0515d6
-- title:
--   Hypergraph: restrict Demand restrict of subset
-- statement:
--   The Hypergraph construction uses the restrict Demand restrict of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L113-L118
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L113-L118

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.restrictDemand_restrict_of_subset (x : ℕ → ℝ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    restrictDemand (restrictDemand x B) A = restrictDemand x A := by sorry
