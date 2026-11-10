-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCq_exists_local_weight_le
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCq_exists_local_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:30:18.329941+00:00
-- url     : https://prove2.me/theorems/224b9bd5-44ca-40bd-83bd-e1c7cc35e5fd
-- title:
--   BDL26 RXLocal Replacement: rx Cq exists local weight le
-- statement:
--   F12 Q-local correction: an actual coboundary preimage with terminal
--   connecting-map weight bounded by the input syndrome weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L234-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L234-L264

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxCq_exists_local_weight_le
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (syndrome : Word Field (QDoubleCylinderEdge P q S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S))) :
    ∃ f : Word Field (QDoubleCylinderVertex P q S),
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f = syndrome ∧
        (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) ≤
          HammingWeight syndrome := by sorry
