-- Prove2me | Theorems.Thm_Paper_Hypergraph_regularized_main_width_comparison
-- name    : Paper.Hypergraph.regularized_main_width_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:54.761975+00:00
-- url     : https://prove2.me/theorems/3ecc51b2-cba0-417b-a0ce-8de1ca923cf2
-- title:
--   Hypergraph: regularized main width comparison
-- statement:
--   The regularized comparison used to derive the manuscript statement.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2608-L2630
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2608-L2630

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.regularized_main_width_comparison (rounding : BalancedRounding) : ∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
    H.fhw ≤ C * H.componentFactor * (H.adw + 1) * Real.log (2 + H.adw) := by sorry
