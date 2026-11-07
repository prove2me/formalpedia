-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_crossCount_unionCayleyGraph_le_degree_card_right
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.crossCount_unionCayleyGraph_le_degree_card_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:51:14.549175+00:00
-- url     : https://prove2.me/theorems/0a03ae8d-f18d-4c67-8fa2-5d2f1ab7de7a
-- title:
--   Left Right Cayley Square Complex: cross Count union Cayley Graph le degree card right
-- statement:
--   The cross count cannot exceed the full incoming degree at its right set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L98-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L98-L113

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.crossCount_unionCayleyGraph_le_degree_card_right
    (X : LeftRightCayleySquareComplex G A B Square) (S T : Finset G) :
    crossCount X.unionCayleyGraph S T ≤
      (Fintype.card A + Fintype.card B) * T.card := by sorry
