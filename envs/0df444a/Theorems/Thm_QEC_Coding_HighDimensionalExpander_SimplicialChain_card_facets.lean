-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_SimplicialChain_card_facets
-- name    : QEC.Coding.HighDimensionalExpander.SimplicialChain.card_facets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:20.555508+00:00
-- url     : https://prove2.me/theorems/27820a1f-5112-4303-aea0-1b7743ee04ce
-- title:
--   Simplicial Chain: card facets
-- statement:
--   The Simplicial Chain construction uses the card facets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L256-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean#L256-L263

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SimplicialChain
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)

theorem QEC.Coding.HighDimensionalExpander.SimplicialChain.card_facets
    (p : Nat) (hp : 1 ≤ p) (τ : Face K (p + 1)) :
    (facets K p τ).card = p + 1 := by sorry
