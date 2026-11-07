-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_rightCayleyGraph_symmetric
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rightCayleyGraph_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:55:36.875201+00:00
-- url     : https://prove2.me/theorems/95e9c133-b222-489f-96db-a7da6a614ffb
-- title:
--   Left Right Cayley Square Complex: right Cayley Graph symmetric
-- statement:
--   The Left Right Cayley Square Complex construction uses the right Cayley Graph symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L129-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L129-L138

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.rightCayleyGraph_symmetric (X : LeftRightCayleySquareComplex G A B Square) :
    IsSymmetric X.rightCayleyGraph := by sorry
