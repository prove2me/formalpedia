-- Prove2me | Theorems.Thm_Paper_Hypergraph_optimalWidth_le_bagWidth
-- name    : Paper.Hypergraph.optimalWidth_le_bagWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:50:07.993846+00:00
-- url     : https://prove2.me/theorems/36b95a9b-f8bc-44ac-8025-7933da837cda
-- title:
--   Hypergraph: optimal Width le bag Width
-- statement:
--   The Hypergraph construction uses the optimal Width le bag Width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L50-L56
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L50-L56

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.optimalWidth_le_bagWidth (H : Hypergraph) (b : Finset ℕ → ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S) {n : ℕ} (D : H.TreeDecomposition n) :
    H.optimalWidth b ≤ D.bagWidth b := by sorry
