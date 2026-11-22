-- Prove2me | Theorems.Thm_Paper_Hypergraph_rounding_structural_bound
-- name    : Paper.Hypergraph.rounding_structural_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:55.525795+00:00
-- url     : https://prove2.me/theorems/76c222c2-6551-4963-808c-9c2825e8accf
-- title:
--   Hypergraph: rounding structural bound
-- statement:
--   The Hypergraph construction uses the rounding structural bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2379-L2394
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2379-L2394

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.rounding_structural_bound (d a : ℕ) :
    min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1 ≤
      9 * (1 + min (d : ℝ) (Real.log (2 + (a : ℝ)))) := by sorry
