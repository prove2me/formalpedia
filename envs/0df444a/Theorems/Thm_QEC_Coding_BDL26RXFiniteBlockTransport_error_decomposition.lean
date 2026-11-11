-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_error_decomposition
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.error_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:29:48.42592+00:00
-- url     : https://prove2.me/theorems/35313b22-9e18-4327-8e87-1ecc1f3547ae
-- title:
--   BDL26 RXFinite Block Transport: error decomposition
-- statement:
--   Internal reconstruction from original labelled restrictions; no decomposition is supplied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L67-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L67-L99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.error_decomposition (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    a+b = (∑ x ∈ X0, extendWordLinear ((rxLx S depth i h).correctionRegion x)
      (restrictWordLinear ((rxLx S depth i h).correctionRegion x) (a+b))) +
      ∑ q ∈ Q0, extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (restrictWordLinear ((rxLq S depth i h).correctionRegion q) (a+b)) := by sorry
