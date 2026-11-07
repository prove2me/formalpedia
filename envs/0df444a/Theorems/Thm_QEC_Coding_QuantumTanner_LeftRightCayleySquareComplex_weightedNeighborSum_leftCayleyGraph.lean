-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_weightedNeighborSum_leftCayleyGraph
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.weightedNeighborSum_leftCayleyGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:55:55.678658+00:00
-- url     : https://prove2.me/theorems/5df3a13a-5c91-475f-83ea-978017924a41
-- title:
--   Left Right Cayley Square Complex: weighted Neighbor Sum left Cayley Graph
-- statement:
--   The Left Right Cayley Square Complex construction uses the weighted Neighbor Sum left Cayley Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L140-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L140-L148

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.weightedNeighborSum_leftCayleyGraph
    (X : LeftRightCayleySquareComplex G A B Square) (f : G → ℝ) (g : G) :
    weightedNeighborSum X.leftCayleyGraph f g = ∑ a, f (X.leftGenerator a * g) := by sorry
