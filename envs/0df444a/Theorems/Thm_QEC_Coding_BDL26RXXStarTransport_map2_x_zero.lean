-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_x_zero
-- name    : QEC.Coding.BDL26RXXStarTransport.map2_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:43:19.617606+00:00
-- url     : https://prove2.me/theorems/9da9c4ba-134a-41d5-aa20-8bab86ffd966
-- title:
--   BDL26 RXXStar Transport: map2 x zero
-- statement:
--   Auxiliary map2 zeroes are proved for the actual selected map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L130-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport/Geometry.lean#L130-L140

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.map2_x_zero (tau : (indexedFamily S depth).Cochain2 i.castSucc)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
      (((indexedDecoderData S depth).selectedMap i).map2 tau)=0 := by sorry
