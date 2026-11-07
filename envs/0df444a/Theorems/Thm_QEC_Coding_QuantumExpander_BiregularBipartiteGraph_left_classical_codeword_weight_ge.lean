-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_left_classical_codeword_weight_ge
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.left_classical_codeword_weight_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:39.946976+00:00
-- url     : https://prove2.me/theorems/3742df0d-ed43-456e-9c46-f94cc98b4de1
-- title:
--   Biregular Bipartite Graph: left classical codeword weight ge
-- statement:
--   LTZ15's classical-distance proposition, first at the level of every
--   nonzero codeword.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L261-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L261-L277

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.left_classical_codeword_weight_ge
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2)
    (x : Word (ZMod 2) A)
    (hxCode : x ∈ (firstCode G.hypergraphProductData).carrier)
    (hx0 : x ≠ 0) :
    γ * Fintype.card A ≤ HammingWeight x := by sorry
