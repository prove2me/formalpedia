-- Prove2me | Theorems.Thm_Paper_Hypergraph_finiteEdgeDistance_congr
-- name    : Paper.Hypergraph.finiteEdgeDistance_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:47.568533+00:00
-- url     : https://prove2.me/theorems/de5e46e0-c808-4db5-b865-1cbf79f6e298
-- title:
--   Hypergraph: finite Edge Distance congr
-- statement:
--   The Hypergraph construction uses the finite Edge Distance congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2248-L2259
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2248-L2259

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.finiteEdgeDistance_congr (H : Hypergraph) (e f : ℕ) {x y : ℕ → ℝ}
    (hxy : ∀ v ∈ H.vertices, x v = y v) : H.finiteEdgeDistance e f x = H.finiteEdgeDistance e f y := by sorry
