-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_extendedNatToENNReal_mono
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.extendedNatToENNReal_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:25.84202+00:00
-- url     : https://prove2.me/theorems/ba0d7486-e29e-4256-8125-275970dba9fb
-- title:
--   Biregular Bipartite Graph: extended Nat To ENNReal mono
-- statement:
--   The embedding of extended natural distances into `ENNReal` is monotone.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L229-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L229-L241

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.extendedNatToENNReal_mono : Monotone extendedNatToENNReal := by sorry
