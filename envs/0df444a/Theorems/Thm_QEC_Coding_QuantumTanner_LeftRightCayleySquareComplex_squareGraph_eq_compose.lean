-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_squareGraph_eq_compose
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_eq_compose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:50:33.133521+00:00
-- url     : https://prove2.me/theorems/a2c0448c-4c93-41f7-8dfe-578e4242c305
-- title:
--   Left Right Cayley Square Complex: square Graph eq compose
-- statement:
--   The actual square adjacency is the product of the two actual Cayley
--   adjacencies, so the product spectral theorem applies to this graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L173-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean#L173-L184

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_compose

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.squareGraph_eq_compose
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) : X.squareGraph side = compose X.leftCayleyGraph X.rightCayleyGraph := by sorry
