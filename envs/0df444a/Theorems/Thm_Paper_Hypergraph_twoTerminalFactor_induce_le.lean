-- Prove2me | Theorems.Thm_Paper_Hypergraph_twoTerminalFactor_induce_le
-- name    : Paper.Hypergraph.twoTerminalFactor_induce_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:31.395608+00:00
-- url     : https://prove2.me/theorems/95249267-9ed9-4e6f-855a-5cdfeeed7ec9
-- title:
--   Hypergraph: two Terminal Factor induce le
-- statement:
--   The Hypergraph construction uses the two Terminal Factor induce le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L43-L51
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L43-L51

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.twoTerminalFactor_induce_le (H : Hypergraph) (Q : Finset ℕ) {R T : Finset ℕ}
    (hTR : T ⊆ R) : (H.induce Q).twoTerminalFactor T ≤ H.twoTerminalFactor R := by sorry
