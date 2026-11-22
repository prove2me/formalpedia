-- Prove2me | Theorems.Thm_Paper_Hypergraph_glue_component_decompositions
-- name    : Paper.Hypergraph.glue_component_decompositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:46.232873+00:00
-- url     : https://prove2.me/theorems/7f01175d-c124-405b-88da-7c485963604a
-- title:
--   Hypergraph: glue component decompositions
-- statement:
--   Glue component decompositions without increasing any bag cost.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1333-L1382
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1333-L1382

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.glue_component_decompositions (H : Hypergraph) (b : Finset ℕ → ℝ) (r : ℝ)
    (hzero : b ∅ ≤ r)
    (hcomp : ∀ C ∈ H.components, ∃ n, ∃ D : (H.induce C).TreeDecomposition n,
      ∀ t, b (D.bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∀ t, b (D.bag t) ≤ r := by sorry
