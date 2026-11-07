-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_weightedNeighborSum_centeredVertexIndicator
-- name    : QEC.Coding.SmallSetExpansion.weightedNeighborSum_centeredVertexIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:24.638117+00:00
-- url     : https://prove2.me/theorems/9ca78be1-07cd-4823-a632-88ea4277140b
-- title:
--   Small Set Expansion: weighted Neighbor Sum centered Vertex Indicator
-- statement:
--   Centering a target indicator turns its neighbor sum into discrepancy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L138-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L138-L167

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.weightedNeighborSum_centeredVertexIndicator
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (T : Finset V) (v : V) :
    weightedNeighborSum M (centeredVertexIndicator T) v =
      Fintype.card V * (∑ u ∈ T, (M v u : ℝ)) -
        degree * T.card := by sorry
