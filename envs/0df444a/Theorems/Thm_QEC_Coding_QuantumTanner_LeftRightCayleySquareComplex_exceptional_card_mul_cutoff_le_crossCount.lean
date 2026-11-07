-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptional_card_mul_cutoff_le_crossCount
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_card_mul_cutoff_le_crossCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:39:16.548197+00:00
-- url     : https://prove2.me/theorems/a3b553ed-83a0-4d80-b01c-ed77b5a9abba
-- title:
--   Left Right Cayley Square Complex: exceptional card mul cutoff le cross Count
-- statement:
--   Exceptional local weights give a genuine full-graph cross-edge lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L137-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L137-L151

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptional_card_mul_cutoff_le_crossCount
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) :
    cutoff * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      crossCount (X.squareGraph side) (X.exceptionalVerticesOnSide side x cutoff)
        (X.activeVerticesOnSide side x) := by sorry
