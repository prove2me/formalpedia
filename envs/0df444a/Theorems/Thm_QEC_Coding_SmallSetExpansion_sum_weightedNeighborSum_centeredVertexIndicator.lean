-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_weightedNeighborSum_centeredVertexIndicator
-- name    : QEC.Coding.SmallSetExpansion.sum_weightedNeighborSum_centeredVertexIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:38.868962+00:00
-- url     : https://prove2.me/theorems/02a1c936-f511-4625-9f37-34aa0c55651c
-- title:
--   Small Set Expansion: sum weighted Neighbor Sum centered Vertex Indicator
-- statement:
--   For a symmetric regular graph, the centered neighbor discrepancy has
--   total zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L171-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L171-L193

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_weightedNeighborSum_centeredVertexIndicator
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (T : Finset V) :
    ∑ v, weightedNeighborSum M (centeredVertexIndicator T) v = 0 := by sorry
