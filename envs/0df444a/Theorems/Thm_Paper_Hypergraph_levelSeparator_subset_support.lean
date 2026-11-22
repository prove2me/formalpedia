-- Prove2me | Theorems.Thm_Paper_Hypergraph_levelSeparator_subset_support
-- name    : Paper.Hypergraph.levelSeparator_subset_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:35.397814+00:00
-- url     : https://prove2.me/theorems/9bcfcf05-2922-4199-aebb-e5febdb25752
-- title:
--   Hypergraph: level Separator subset support
-- statement:
--   The Hypergraph construction uses the level Separator subset support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L133-L136
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L133-L136

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.levelSeparator_subset_support (H : Hypergraph) (x d : ℕ → ℝ) (r : ℝ) :
    H.levelSeparator x d r ⊆ H.vertices.filter (fun v => x v ≠ 0) := by sorry
