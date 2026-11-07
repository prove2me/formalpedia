-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_supportSquareGraph_eq_zero_of_not_active
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.supportSquareGraph_eq_zero_of_not_active
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:38:33.274528+00:00
-- url     : https://prove2.me/theorems/f308ddbe-38e7-4d93-9722-51d52e5ad49a
-- title:
--   Left Right Cayley Square Complex: support Square Graph eq zero of not active
-- statement:
--   A selected edge ends only at an actually active vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L94-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L94-L107

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.supportSquareGraph_eq_zero_of_not_active
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g h : G)
    (hh : h ∉ X.activeVerticesOnSide side x) : X.supportSquareGraph side x g h = 0 := by sorry
