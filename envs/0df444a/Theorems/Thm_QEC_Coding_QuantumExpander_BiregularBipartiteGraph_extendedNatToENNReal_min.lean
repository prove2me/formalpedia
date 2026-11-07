-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_extendedNatToENNReal_min
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.extendedNatToENNReal_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:32:22.649213+00:00
-- url     : https://prove2.me/theorems/7990e154-9046-41a7-84d9-d287ac79691e
-- title:
--   Biregular Bipartite Graph: extended Nat To ENNReal min
-- statement:
--   The real-valued embedding preserves binary minima.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L388-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L388-L394

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.extendedNatToENNReal_min (m n : WithTop Nat) :
    extendedNatToENNReal (min m n) =
      min (extendedNatToENNReal m) (extendedNatToENNReal n) := by sorry
