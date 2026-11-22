-- Prove2me | Theorems.Thm_Paper_Hypergraph_terminals_subset_separatorRegion
-- name    : Paper.Hypergraph.terminals_subset_separatorRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:55.49669+00:00
-- url     : https://prove2.me/theorems/3e009202-96f5-44ae-87d5-f487005f246a
-- title:
--   Hypergraph: terminals subset separator Region
-- statement:
--   The Hypergraph construction uses the terminals subset separator Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L22-L26
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L22-L26

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.terminals_subset_separatorRegion (H : Hypergraph) {A S : Finset ℕ}
    (hA : A ⊆ H.vertices) : A \ S ⊆ H.separatorRegion A S := by sorry
