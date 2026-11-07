-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_activeVerticesOnSide_nonempty_of_ne_zero
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVerticesOnSide_nonempty_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:58:35.384719+00:00
-- url     : https://prove2.me/theorems/1f9739b7-c157-49dd-b8d6-8d7f3476f2f6
-- title:
--   Left Right Cayley Square Complex: active Vertices On Side nonempty of ne zero
-- statement:
--   A nonzero global word has a nonzero local view on each side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalDescent.lean#L24-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LocalDescent.lean#L24-L34

import Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.activeVerticesOnSide_nonempty_of_ne_zero
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (hx : x ≠ 0) :
    (X.activeVerticesOnSide side x).Nonempty := by sorry
