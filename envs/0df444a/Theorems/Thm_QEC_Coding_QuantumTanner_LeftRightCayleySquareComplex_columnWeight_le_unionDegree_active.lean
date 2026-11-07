-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_columnWeight_le_unionDegree_active
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.columnWeight_le_unionDegree_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:52:16.667671+00:00
-- url     : https://prove2.me/theorems/94d79ff0-561b-4b23-8e95-80c5cb15b88b
-- title:
--   Left Right Cayley Square Complex: column Weight le union Degree active
-- statement:
--   The corresponding column count uses left-edge labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L161-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L161-L174

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.columnWeight_le_unionDegree_active
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (b : B) :
    HammingWeight (columnRestriction b (X.localRestriction (g, side) x)) ≤
      ∑ h ∈ X.activeVerticesOnSide (!side) x, X.unionCayleyGraph g h := by sorry
