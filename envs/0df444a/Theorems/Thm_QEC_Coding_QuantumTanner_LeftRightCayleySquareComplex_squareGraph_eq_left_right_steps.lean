-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_eq_left_right_steps
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_eq_left_right_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:54:20.481996+00:00
-- url     : https://prove2.me/theorems/9f421c86-e784-45fe-bbae-4ff80fb7c21d
-- title:
--   Left Right Cayley Square Complex: square Graph eq left right steps
-- statement:
--   The weighted square adjacency counts precisely the pairs of left/right
--   labels taking the base vertex to the target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L71-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L71-L96

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_eq_left_right_steps
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (g h : G) :
    X.squareGraph side g h =
      (Finset.univ.filter fun ab : A × B => X.leftGenerator ab.1 * g * X.rightGenerator ab.2 = h).card := by sorry
