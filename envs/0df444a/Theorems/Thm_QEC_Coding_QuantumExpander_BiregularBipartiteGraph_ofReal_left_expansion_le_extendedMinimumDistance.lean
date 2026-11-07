-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_ofReal_left_expansion_le_extendedMinimumDistance
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ofReal_left_expansion_le_extendedMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:47.707048+00:00
-- url     : https://prove2.me/theorems/bfb0c9b2-97e2-48af-b5c7-8bb0c9813814
-- title:
--   Biregular Bipartite Graph: of Real left expansion le extended Minimum Distance
-- statement:
--   The left classical-distance bound in the same `ENNReal` domain used by
--   the final real-valued LTZ15 conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L297-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L297-L313

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ofReal_left_expansion_le_extendedMinimumDistance
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2) :
    ENNReal.ofReal (γ * Fintype.card A) ≤
      extendedNatToENNReal
        (extendedMinimumDistance (firstCode G.hypergraphProductData)) := by sorry
