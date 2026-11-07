-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_rightCayleyGraph_regular
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rightCayleyGraph_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:55:04.309207+00:00
-- url     : https://prove2.me/theorems/9e7f9f3b-fc51-42d8-845e-ab438e3811c9
-- title:
--   Left Right Cayley Square Complex: right Cayley Graph regular
-- statement:
--   The Left Right Cayley Square Complex construction uses the right Cayley Graph regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L112-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L112-L116

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rightCayleyGraph_regular (X : LeftRightCayleySquareComplex G A B Square) :
    IsRegular X.rightCayleyGraph (Fintype.card B) := by sorry
