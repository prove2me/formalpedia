-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_sum_leftInducedDegree
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.sum_leftInducedDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:48.405144+00:00
-- url     : https://prove2.me/theorems/da0eb335-185e-4840-8d29-bc725c118202
-- title:
--   Biregular Bipartite Graph: sum left Induced Degree
-- statement:
--   Double-count the edges from `S` to its right neighbors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L106-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L106-L115

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.sum_leftInducedDegree
    (G : BiregularBipartiteGraph A B) (S : Finset A) :
    ∑ b, G.leftInducedDegree S b = S.card * G.leftDegree := by sorry
