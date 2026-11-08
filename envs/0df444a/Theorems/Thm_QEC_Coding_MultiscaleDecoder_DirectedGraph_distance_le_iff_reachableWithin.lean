-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_DirectedGraph_distance_le_iff_reachableWithin
-- name    : QEC.Coding.MultiscaleDecoder.DirectedGraph.distance_le_iff_reachableWithin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:43:23.255267+00:00
-- url     : https://prove2.me/theorems/244dceb7-9953-4929-9ca3-11b7b8e4c4ef
-- title:
--   Directed Graph: distance le iff reachable Within
-- statement:
--   The executable distance detects every radius within its finite budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L83-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L83-L106

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.DirectedGraph
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]

theorem QEC.Coding.MultiscaleDecoder.DirectedGraph.distance_le_iff_reachableWithin (G : DirectedGraph V) (u v : V)
    (r : Nat) (hr : r ≤ Fintype.card V) :
    G.distance u v ≤ (r : WithTop Nat) ↔ G.reachableWithin r u v = true := by sorry
