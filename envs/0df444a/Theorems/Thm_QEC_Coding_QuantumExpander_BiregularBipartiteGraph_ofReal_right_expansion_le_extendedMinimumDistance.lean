-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_ofReal_right_expansion_le_extendedMinimumDistance
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ofReal_right_expansion_le_extendedMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:31:33.824029+00:00
-- url     : https://prove2.me/theorems/77c65995-005c-4d19-9d9b-84a6014e3c7e
-- title:
--   Biregular Bipartite Graph: of Real right expansion le extended Minimum Distance
-- statement:
--   The right expansion bound is the left bound for the transposed incidence
--   matrix, hence controls LTZ15's transpose distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L317-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L317-L323

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ofReal_right_expansion_le_extendedMinimumDistance
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.RightExpanding γ δ) (hδ : δ < 1 / 2) :
    ENNReal.ofReal (γ * Fintype.card B) ≤
      extendedNatToENNReal
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by sorry
