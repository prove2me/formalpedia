-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported
-- name    : QEC.Coding.BDL26RXXStarTransport.correction_difference_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:00:17.012912+00:00
-- url     : https://prove2.me/theorems/02dc7c99-ba79-415a-8c07-09c9ea47a2c9
-- title:
--   BDL26 RXXStar Transport: correction difference supported
-- statement:
--   Cancel every component of the same original canonical correction outside the star.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L106-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L106-L136

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.correction_difference_supported (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    hammingSupport ((run S depth i h a).correction+(run S depth i h b).correction) ⊆
      star1 S depth i h x := by sorry
