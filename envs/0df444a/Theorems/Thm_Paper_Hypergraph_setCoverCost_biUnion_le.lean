-- Prove2me | Theorems.Thm_Paper_Hypergraph_setCoverCost_biUnion_le
-- name    : Paper.Hypergraph.setCoverCost_biUnion_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:40.840098+00:00
-- url     : https://prove2.me/theorems/302c5dff-0ce7-4c68-83ae-af81d3a6bcf0
-- title:
--   Hypergraph: set Cover Cost bi Union le
-- statement:
--   Subadditivity for the final union of separators.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L203-L214
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean#L203-L214

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.setCoverCost_biUnion_le (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (S : ι → Finset ℕ) :
    H.setCoverCost (I.biUnion S) ≤ ∑ i ∈ I, H.setCoverCost (S i) := by sorry
