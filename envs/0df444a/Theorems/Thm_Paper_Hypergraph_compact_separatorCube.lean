-- Prove2me | Theorems.Thm_Paper_Hypergraph_compact_separatorCube
-- name    : Paper.Hypergraph.compact_separatorCube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:26.484822+00:00
-- url     : https://prove2.me/theorems/5efc7280-b328-43d8-a243-f2d614267bbd
-- title:
--   Hypergraph: compact separator Cube
-- statement:
--   The Hypergraph construction uses the compact separator Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2202-L2211
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2202-L2211

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.compact_separatorCube (H : Hypergraph) (γ : ℕ → ℝ) (θ : ℝ) :
    IsCompact (H.separatorCube γ θ) := by sorry
