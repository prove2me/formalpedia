-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_adjacencyPairing_centeredVertexIndicator
-- name    : QEC.Coding.SmallSetExpansion.adjacencyPairing_centeredVertexIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:32:39.09185+00:00
-- url     : https://prove2.me/theorems/844655dd-6d9d-4920-a8a9-f5537cfa6841
-- title:
--   Small Set Expansion: adjacency Pairing centered Vertex Indicator
-- statement:
--   Exact discrepancy identity for two division-free centered indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L196-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean#L196-L223

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.adjacencyPairing_centeredVertexIndicator
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (S T : Finset V) :
    adjacencyPairing M
        (centeredVertexIndicator S) (centeredVertexIndicator T) =
      (Fintype.card V : ℝ) *
        ((Fintype.card V : ℝ) * crossCount M S T -
          degree * (S.card : ℝ) * T.card) := by sorry
