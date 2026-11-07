-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_sum_supportSquareGraph_eq_localWeight
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_supportSquareGraph_eq_localWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:02:21.657887+00:00
-- url     : https://prove2.me/theorems/ebb58ead-a5ad-4b90-a502-e2a9126196c0
-- title:
--   Left Right Cayley Square Complex: sum support Square Graph eq local Weight
-- statement:
--   Degree in the selected square graph is exactly the actual local weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L67-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L67-L91

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.sum_supportSquareGraph_eq_localWeight
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g : G) :
    (∑ h : G, X.supportSquareGraph side x g h) =
      HammingWeight (X.localRestriction (g, side) x) := by sorry
