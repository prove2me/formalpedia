-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_hammingSupport_nonempty_of_ne_zero
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.hammingSupport_nonempty_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:23:58.454475+00:00
-- url     : https://prove2.me/theorems/ff5e3ee8-7a75-4831-84ea-610061aa9fcc
-- title:
--   Biregular Bipartite Graph: hamming Support nonempty of ne zero
-- statement:
--   A nonzero finite word has nonempty Hamming support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L245-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L245-L257

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
omit [DecidableEq A]

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.hammingSupport_nonempty_of_ne_zero
    (x : Word (ZMod 2) A) (hx : x ≠ 0) :
    (hammingSupport x).Nonempty := by sorry
