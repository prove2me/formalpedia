-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_quantumDistance_expansion_bound
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.quantumDistance_expansion_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:01:46.031756+00:00
-- url     : https://prove2.me/theorems/a86e4443-7cb1-4c4f-a3dc-dd8d50e2020a
-- title:
--   Biregular Bipartite Graph: quantum Distance expansion bound
-- statement:
--   The LTZ15 expansion lower bound for the exact diagonal quantum distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L483-L500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L483-L500

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.quantumDistance_expansion_bound
    (G : BiregularBipartiteGraph A B)
    {γA δA γB δB : Real}
    (hExpand : G.LeftRightExpanding γA δA γB δB)
    (hδA : δA < 1 / 2) (hδB : δB < 1 / 2) :
    ENNReal.ofReal
        (min (γA * Fintype.card A) (γB * Fintype.card B)) ≤
      extendedNatToENNReal
        (extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode G.hypergraphProductData).xCode
          (binaryCSSCode G.hypergraphProductData).zCode) := by sorry
