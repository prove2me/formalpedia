-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_rowWeight_incidenceMatrix
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.rowWeight_incidenceMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:03:29.453328+00:00
-- url     : https://prove2.me/theorems/7c44538b-4f2d-4fc9-ac04-5c144d429b12
-- title:
--   Biregular Bipartite Graph: row Weight incidence Matrix
-- statement:
--   Every row of the graph incidence matrix has the right degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L428-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L428-L432

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.rowWeight_incidenceMatrix
    (G : BiregularBipartiteGraph A B) (b : B) :
    rowWeight G.incidenceMatrix b = G.rightDegree := by sorry
