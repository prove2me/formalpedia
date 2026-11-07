-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_unionCayleyGraph_regular
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.unionCayleyGraph_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:50:55.934688+00:00
-- url     : https://prove2.me/theorems/b604c6d2-5556-43ac-a916-f5171c9ea54e
-- title:
--   Left Right Cayley Square Complex: union Cayley Graph regular
-- statement:
--   The union has the sum of the local generator degrees.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L43-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L43-L47

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.unionCayleyGraph_regular (X : LeftRightCayleySquareComplex G A B Square) :
    IsRegular X.unionCayleyGraph (Fintype.card A + Fintype.card B) := by sorry
