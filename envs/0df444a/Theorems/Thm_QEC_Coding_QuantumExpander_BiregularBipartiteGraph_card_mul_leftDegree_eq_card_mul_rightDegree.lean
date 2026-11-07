-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_card_mul_leftDegree_eq_card_mul_rightDegree
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.card_mul_leftDegree_eq_card_mul_rightDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:34:45.700626+00:00
-- url     : https://prove2.me/theorems/f0cce8d9-1dc3-44a0-8b35-11b63db02056
-- title:
--   Biregular Bipartite Graph: card mul left Degree eq card mul right Degree
-- statement:
--   Double-counting all edges gives the biregular degree-balance identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L397-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L397-L405

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.card_mul_leftDegree_eq_card_mul_rightDegree
    (G : BiregularBipartiteGraph A B) :
    Fintype.card A * G.leftDegree = Fintype.card B * G.rightDegree := by sorry
