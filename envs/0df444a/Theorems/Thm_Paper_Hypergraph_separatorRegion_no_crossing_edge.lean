-- Prove2me | Theorems.Thm_Paper_Hypergraph_separatorRegion_no_crossing_edge
-- name    : Paper.Hypergraph.separatorRegion_no_crossing_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:48.54884+00:00
-- url     : https://prove2.me/theorems/07cf681c-b8a1-40d1-afd7-104d09c577b0
-- title:
--   Hypergraph: separator Region no crossing edge
-- statement:
--   The Hypergraph construction uses the separator Region no crossing edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L42-L55
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L42-L55

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.separatorRegion_no_crossing_edge (H : Hypergraph) (A S : Finset ℕ)
    {e : ℕ} (he : e ∈ H.edges) :
    Disjoint (H.edge e) (H.separatorRegion A S) ∨
      Disjoint (H.edge e) (H.vertices \ (H.separatorRegion A S ∪ S)) := by sorry
