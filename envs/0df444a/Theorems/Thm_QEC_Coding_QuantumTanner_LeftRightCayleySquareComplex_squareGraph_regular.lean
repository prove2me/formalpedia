-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_regular
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:38:40.887935+00:00
-- url     : https://prove2.me/theorems/aa7b36c3-4789-4620-af17-482dfb824d00
-- title:
--   Left Right Cayley Square Complex: square Graph regular
-- statement:
--   The full square graph has the product of the two local degrees.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L121-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L121-L128

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_regular (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) : IsRegular (X.squareGraph side) (Fintype.card A * Fintype.card B) := by sorry
