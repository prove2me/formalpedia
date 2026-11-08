-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_DirectedGraph_distanceAux_exists_of_reachableWithin
-- name    : QEC.Coding.MultiscaleDecoder.DirectedGraph.distanceAux_exists_of_reachableWithin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:18:06.125838+00:00
-- url     : https://prove2.me/theorems/85b28ca9-4a6c-4f8f-92a8-f356a2ae9373
-- title:
--   Directed Graph: distance Aux exists of reachable Within
-- statement:
--   A reachable target makes the bounded search succeed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L56-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/DirectedDistance.lean#L56-L66

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.DirectedGraph
universe v
variable {V : Type v} [Fintype V] [DecidableEq V]

theorem QEC.Coding.MultiscaleDecoder.DirectedGraph.distanceAux_exists_of_reachableWithin (G : DirectedGraph V) (u v : V)
    (steps : Nat) (h : G.reachableWithin steps u v = true) :
    ∃ n, G.distanceAux u v steps = some n ∧ n ≤ steps := by sorry
