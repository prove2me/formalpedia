-- Prove2me | Theorems.Thm_Paper_Hypergraph_optimalWidth_le_components
-- name    : Paper.Hypergraph.optimalWidth_le_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:50.035946+00:00
-- url     : https://prove2.me/theorems/52dcaf12-88bc-4f8b-a423-fdf8202cda9b
-- title:
--   Hypergraph: optimal Width le components
-- statement:
--   Passing to infima after gluing needs no attainment of optimal decompositions.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1395-L1414
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1395-L1414

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.optimalWidth_le_components (H : Hypergraph) (b : Finset ℕ → ℝ) (r : ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S) (hzero : b ∅ ≤ r)
    (hcomp : ∀ C ∈ H.components, (H.induce C).optimalWidth b ≤ r) :
    H.optimalWidth b ≤ r := by sorry
