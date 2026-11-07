-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_supportSquareGraph_le_squareGraph
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.supportSquareGraph_le_squareGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:37:36.243874+00:00
-- url     : https://prove2.me/theorems/2569dafd-2925-49f5-bc1c-51f2cd128c82
-- title:
--   Left Right Cayley Square Complex: support Square Graph le square Graph
-- statement:
--   The Left Right Cayley Square Complex construction uses the support Square Graph le square Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L43-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean#L43-L49

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.supportSquareGraph_le_squareGraph
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (g h : G) :
    X.supportSquareGraph side x g h ≤ X.squareGraph side g h := by sorry
