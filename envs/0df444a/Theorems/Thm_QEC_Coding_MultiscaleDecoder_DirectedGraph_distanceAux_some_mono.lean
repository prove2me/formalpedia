-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_DirectedGraph_distanceAux_some_mono
-- name    : QEC.Coding.MultiscaleDecoder.DirectedGraph.distanceAux_some_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:18:07.845427+00:00
-- url     : https://prove2.me/theorems/02f170a9-a2bd-4088-834e-ca1f7e02aea9
-- title:
--   Directed Graph: distance Aux some mono
-- statement:
--   Once a distance is found, extending the search keeps that result.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L69-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L69-L80

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.DirectedGraph
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]

theorem QEC.Coding.MultiscaleDecoder.DirectedGraph.distanceAux_some_mono (G : DirectedGraph V) (u v : V)
    {a b n : Nat} (hab : a ≤ b) (h : G.distanceAux u v a = some n) :
    G.distanceAux u v b = some n := by sorry
