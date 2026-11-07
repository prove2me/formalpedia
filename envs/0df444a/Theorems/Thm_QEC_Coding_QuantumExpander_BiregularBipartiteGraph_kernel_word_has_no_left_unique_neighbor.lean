-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_kernel_word_has_no_left_unique_neighbor
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.kernel_word_has_no_left_unique_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:36.689013+00:00
-- url     : https://prove2.me/theorems/57547d58-0f0c-41b4-8eed-7c97dd22ec49
-- title:
--   Biregular Bipartite Graph: kernel word has no left unique neighbor
-- statement:
--   A binary kernel word cannot have a unique neighbor in its support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L182-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L182-L214

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.kernel_word_has_no_left_unique_neighbor
    (G : BiregularBipartiteGraph A B) (x : Word (ZMod 2) A)
    (hxKernel : Matrix.toLin' G.incidenceMatrix x = 0) (b : B) :
    G.leftInducedDegree (hammingSupport x) b ≠ 1 := by sorry
