-- Prove2me | Theorems.Thm_Paper_Hypergraph_coverCost_induce_restrictDemand
-- name    : Paper.Hypergraph.coverCost_induce_restrictDemand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:08.844369+00:00
-- url     : https://prove2.me/theorems/f098e19a-3063-4650-8d9a-68baec20a01d
-- title:
--   Hypergraph: cover Cost induce restrict Demand
-- statement:
--   Ambient and induced cover costs agree after restricting the demand.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L102-L141
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L102-L141

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.coverCost_induce_restrictDemand (H : Hypergraph) (z : ℕ → ℝ) (Q : Finset ℕ) :
    (H.induce Q).coverCost z = H.coverCost (restrictDemand z Q) := by sorry
