-- Prove2me | Theorems.Thm_Paper_Hypergraph_separatorRegion_closed
-- name    : Paper.Hypergraph.separatorRegion_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:38.420952+00:00
-- url     : https://prove2.me/theorems/7e61e5b8-4a61-48e7-8785-b837fd74de24
-- title:
--   Hypergraph: separator Region closed
-- statement:
--   The Hypergraph construction uses the separator Region closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L35-L40
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L35-L40

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.separatorRegion_closed (H : Hypergraph) (A S : Finset ℕ) {u v : ℕ}
    (hu : u ∈ H.separatorRegion A S) (hv : v ∈ H.vertices \ S)
    (huv : H.primal.Adj u v) : v ∈ H.separatorRegion A S := by sorry
