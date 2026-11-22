-- Prove2me | Theorems.Thm_Paper_Hypergraph_manuscript_rounding_cost_bound
-- name    : Paper.Hypergraph.manuscript_rounding_cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:56.139143+00:00
-- url     : https://prove2.me/theorems/cc567aaa-90fa-4144-9d94-c1626053e754
-- title:
--   Hypergraph: manuscript rounding cost bound
-- statement:
--   The sharp cost factor in the manuscript's half-balanced specialization.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingComplete.lean#L31-L63
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingComplete.lean#L31-L63

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.manuscript_rounding_cost_bound {q : ℝ} (hq : 0 ≤ q) :
    ((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ))) * q ≤
      120 * q * (Real.log (max 2 q) / Real.log 2) := by sorry
