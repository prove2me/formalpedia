-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_incoming_regular
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.unionCayleyGraph_incoming_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:31:20.64519+00:00
-- url     : https://prove2.me/theorems/f18058c7-2f4f-4936-a855-cc47ddc1fa1c
-- title:
--   Left Right Cayley Square Complex: union Cayley Graph incoming regular
-- statement:
--   Every target receives one edge per generator label, counting multiplicities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L71-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L71-L95

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.unionCayleyGraph_incoming_regular
    (X : LeftRightCayleySquareComplex G A B Square) (h : G) :
    (∑ g : G, X.unionCayleyGraph g h) = Fintype.card A + Fintype.card B := by sorry
