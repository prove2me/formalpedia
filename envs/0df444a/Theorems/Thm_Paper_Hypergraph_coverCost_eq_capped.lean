-- Prove2me | Theorems.Thm_Paper_Hypergraph_coverCost_eq_capped
-- name    : Paper.Hypergraph.coverCost_eq_capped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:48.183656+00:00
-- url     : https://prove2.me/theorems/cd92fc2f-e944-4edc-98f2-df1900f588d1
-- title:
--   Hypergraph: cover Cost eq capped
-- statement:
--   The cover cost agrees with the cited paper's coefficients in [0,1].
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L117-L136
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L117-L136

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.coverCost_eq_capped (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) :
    H.coverCost x = sInf {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e} := by sorry
