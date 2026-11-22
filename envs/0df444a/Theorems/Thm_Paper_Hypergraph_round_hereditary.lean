-- Prove2me | Theorems.Thm_Paper_Hypergraph_round_hereditary
-- name    : Paper.Hypergraph.round_hereditary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:16.888223+00:00
-- url     : https://prove2.me/theorems/6767c74d-95f3-43f3-939c-e8f4b3712b28
-- title:
--   Hypergraph: round hereditary
-- statement:
--   The Hypergraph construction uses the round hereditary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2507-L2561
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2507-L2561

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.round_hereditary (rounding : BalancedRounding) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ H : Hypergraph,
    H.Connected → H.sep (5 / 6) ≤ C₁ * H.structuralFactor *
      (H.fsep (1 / 2) + 1) * Real.log (2 + H.fsep (1 / 2)) := by sorry
