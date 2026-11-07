-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_quantumDistance_eq_min_classicalDistances
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.quantumDistance_eq_min_classicalDistances
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:31:15.063769+00:00
-- url     : https://prove2.me/theorems/764e8478-d31a-4553-95a1-18a6159182ad
-- title:
--   Biregular Bipartite Graph: quantum Distance eq min classical Distances
-- statement:
--   The exact LTZ15 diagonal quantum distance, without a full-rank
--   assumption on the incidence matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L339-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L339-L385

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.quantumDistance_eq_min_classicalDistances
    (G : BiregularBipartiteGraph A B) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode G.hypergraphProductData).xCode
        (binaryCSSCode G.hypergraphProductData).zCode =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by sorry
