-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_finrank_middleHomology_ge_card_sub_sq
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.finrank_middleHomology_ge_card_sub_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:02:38.724247+00:00
-- url     : https://prove2.me/theorems/6e0ee076-c18f-4f84-b66b-5d8a8638dfea
-- title:
--   Biregular Bipartite Graph: finrank middle Homology ge card sub sq
-- statement:
--   The diagonal HGP dimension formula implies the LTZ15 lower bound
--   `K ≥ (n_A - n_B)²` without a rank assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L452-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L452-L479

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.finrank_middleHomology_ge_card_sub_sq
    (G : BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A) :
    (Fintype.card A - Fintype.card B) ^ 2 ≤
      Module.finrank (ZMod 2) (chainComplex G.hypergraphProductData).middleHomology := by sorry
