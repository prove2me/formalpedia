-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_inputDistanceMinimum_hypergraphProductData
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.inputDistanceMinimum_hypergraphProductData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:32:04.341091+00:00
-- url     : https://prove2.me/theorems/ea13286a-b48b-4515-a685-8726e148edcb
-- title:
--   Biregular Bipartite Graph: input Distance Minimum hypergraph Product Data
-- statement:
--   For diagonal HGP data, the four-input distance minimum reduces exactly
--   to the minimum of the incidence code and its transpose code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L327-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L327-L335

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.inputDistanceMinimum_hypergraphProductData
    (G : BiregularBipartiteGraph A B) :
    inputDistanceMinimum G.hypergraphProductData =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by sorry
