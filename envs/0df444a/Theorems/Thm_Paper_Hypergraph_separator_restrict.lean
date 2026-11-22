-- Prove2me | Theorems.Thm_Paper_Hypergraph_separator_restrict
-- name    : Paper.Hypergraph.separator_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:46.786808+00:00
-- url     : https://prove2.me/theorems/27c641bf-6fd0-46f1-aabb-cbe2775d7228
-- title:
--   Hypergraph: separator restrict
-- statement:
--   Zero extension on ambient coordinates preserves all separator constraints.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2262-L2280
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2262-L2280

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.separator_restrict (H : Hypergraph) {γ x : ℕ → ℝ} {θ : ℝ}
    (hx : H.FractionalBalanced γ θ x) :
    (fun v => if v ∈ H.vertices then x v else 0) ∈ H.separatorCube γ θ := by sorry
