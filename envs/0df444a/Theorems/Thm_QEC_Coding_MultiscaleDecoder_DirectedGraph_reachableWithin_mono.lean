-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_DirectedGraph_reachableWithin_mono
-- name    : QEC.Coding.MultiscaleDecoder.DirectedGraph.reachableWithin_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:17:49.185764+00:00
-- url     : https://prove2.me/theorems/f8192545-7a32-445f-be52-dff034f0967c
-- title:
--   Directed Graph: reachable Within mono
-- statement:
--   Increasing the path-length budget preserves reachability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L18-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L18-L28

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.DirectedGraph
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]

theorem QEC.Coding.MultiscaleDecoder.DirectedGraph.reachableWithin_mono (G : DirectedGraph V) (u v : V)
    {m n : Nat} (hmn : m ≤ n) (h : G.reachableWithin m u v = true) :
    G.reachableWithin n u v = true := by sorry
