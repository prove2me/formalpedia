-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_lower_weight_le_seven_error
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.lower_weight_le_seven_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:26:29.418198+00:00
-- url     : https://prove2.me/theorems/e0937057-ba57-49da-9f08-296b3c4eee1b
-- title:
--   BDL26 RXActive Error Transport: lower weight le seven error
-- statement:
--   Unconditional single-step bound by original physical ERROR weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L374-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L374-L379

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXActiveErrorTransport.lower_weight_le_seven_error (a b : Upper S depth i) :
    HammingWeight (L S depth i h a b) ≤ 7*HammingWeight (a+b) := by sorry
