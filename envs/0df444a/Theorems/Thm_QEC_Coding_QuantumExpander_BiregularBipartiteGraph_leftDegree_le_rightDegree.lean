-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_leftDegree_le_rightDegree
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.leftDegree_le_rightDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:00:50.846196+00:00
-- url     : https://prove2.me/theorems/91a57c15-f9ca-4565-9465-99ed02555767
-- title:
--   Biregular Bipartite Graph: left Degree le right Degree
-- statement:
--   With nonempty parts and positive degrees, `n_B ≤ n_A` implies the
--   degree order `Δ_A ≤ Δ_B` stated by LTZ15.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L409-L425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L409-L425

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.leftDegree_le_rightDegree
    (G : BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A) :
    G.leftDegree ≤ G.rightDegree := by sorry
