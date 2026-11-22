-- Prove2me | Theorems.Thm_Paper_Hypergraph_recursive_separator_decomposition
-- name    : Paper.Hypergraph.recursive_separator_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:53:56.817558+00:00
-- url     : https://prove2.me/theorems/203c7781-2015-43d5-9a22-cbcbdda1fbac
-- title:
--   Hypergraph: recursive separator decomposition
-- statement:
--   The Hypergraph construction uses the recursive separator decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2028-L2057
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2028-L2057

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.recursive_separator_decomposition (H : Hypergraph) {η : ℝ}
    (hη : 0 < η ∧ η < 1) :
    H.fhw ≤ (2 - η) / (1 - η) * (H.sep η + 1) := by sorry
