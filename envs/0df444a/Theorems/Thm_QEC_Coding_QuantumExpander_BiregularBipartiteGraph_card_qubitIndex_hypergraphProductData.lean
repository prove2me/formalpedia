-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_card_qubitIndex_hypergraphProductData
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.card_qubitIndex_hypergraphProductData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:04:24.834976+00:00
-- url     : https://prove2.me/theorems/de24e808-eb5a-404c-9a31-b360377b0ac0
-- title:
--   Biregular Bipartite Graph: card qubit Index hypergraph Product Data
-- statement:
--   The exact diagonal HGP blocklength for the LTZ15 incidence matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L442-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L442-L448

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.card_qubitIndex_hypergraphProductData
    (_G : BiregularBipartiteGraph A B) :
    Fintype.card (QubitIndex B A B A) =
      Fintype.card A ^ 2 + Fintype.card B ^ 2 := by sorry
