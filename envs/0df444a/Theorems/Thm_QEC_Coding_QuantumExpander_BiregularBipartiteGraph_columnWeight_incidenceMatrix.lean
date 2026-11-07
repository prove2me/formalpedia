-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_columnWeight_incidenceMatrix
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.columnWeight_incidenceMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:01:54.429687+00:00
-- url     : https://prove2.me/theorems/79c8cb4f-6a0f-4d3f-9d21-3f8f11853c70
-- title:
--   Biregular Bipartite Graph: column Weight incidence Matrix
-- statement:
--   Every column of the graph incidence matrix has the left degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L435-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L435-L439

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.columnWeight_incidenceMatrix
    (G : BiregularBipartiteGraph A B) (a : A) :
    columnWeight G.incidenceMatrix a = G.leftDegree := by sorry
