-- Prove2me | Theorems.Thm_Paper_Hypergraph_roundingBall_mono
-- name    : Paper.Hypergraph.roundingBall_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:55:29.399788+00:00
-- url     : https://prove2.me/theorems/8d5a76e3-b33c-4e8f-bd47-89eaa8b51f89
-- title:
--   Hypergraph: rounding Ball mono
-- statement:
--   The Hypergraph construction uses the rounding Ball mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L137-L140
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingPaths.lean#L137-L140

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.roundingBall_mono (H : Hypergraph) (x : ℕ → ℝ) (Q : Finset ℕ) (c : ℕ)
    {a b : ℝ} (hab : a ≤ b) : H.roundingBall x Q c a ⊆ H.roundingBall x Q c b := by sorry
