-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_weightedNeighborSum_squareGraph
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.weightedNeighborSum_squareGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:54:38.703363+00:00
-- url     : https://prove2.me/theorems/ab9671ca-e59e-4600-9e2b-5d8390557e52
-- title:
--   Left Right Cayley Square Complex: weighted Neighbor Sum square Graph
-- statement:
--   The Left Right Cayley Square Complex construction uses the weighted Neighbor Sum square Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L160-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L160-L169

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.weightedNeighborSum_squareGraph
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (f : G → ℝ) (g : G) :
    weightedNeighborSum (X.squareGraph side) f g =
      ∑ a, ∑ b, f (X.leftGenerator a * g * X.rightGenerator b) := by sorry
