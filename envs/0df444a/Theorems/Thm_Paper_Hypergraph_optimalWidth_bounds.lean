-- Prove2me | Theorems.Thm_Paper_Hypergraph_optimalWidth_bounds
-- name    : Paper.Hypergraph.optimalWidth_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:30.193854+00:00
-- url     : https://prove2.me/theorems/2c845ba2-3ecb-4597-aca5-57452abc827b
-- title:
--   Hypergraph: optimal Width bounds
-- statement:
--   Lower bounds pass to the optimum; the one-bag tree supplies an upper bound.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L35-L48
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L35-L48

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.optimalWidth_bounds (H : Hypergraph) (b : Finset ℕ → ℝ) {L : ℝ}
    (hb : ∀ S ⊆ H.vertices, L ≤ b S) :
    L ≤ H.optimalWidth b ∧ H.optimalWidth b ≤ b H.vertices := by sorry
