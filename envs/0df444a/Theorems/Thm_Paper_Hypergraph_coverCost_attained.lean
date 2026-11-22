-- Prove2me | Theorems.Thm_Paper_Hypergraph_coverCost_attained
-- name    : Paper.Hypergraph.coverCost_attained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:42.725804+00:00
-- url     : https://prove2.me/theorems/8f88a9ed-5d09-41f2-914e-91f2c798c5b0
-- title:
--   Hypergraph: cover Cost attained
-- statement:
--   The minimum cover cost is attained, with coefficients in [0,1].
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L139-L188
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L139-L188

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.coverCost_attained (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) :
    ∃ y, H.Cover x y ∧ (∀ e ∈ H.edges, y e ≤ 1) ∧
      H.coverCost x = ∑ e ∈ H.edges, y e := by sorry
