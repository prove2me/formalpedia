-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_inactive_q_iff
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.inactive_q_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:37:14.585203+00:00
-- url     : https://prove2.me/theorems/d00486bd-f4ca-4272-8b52-d7591aa582a5
-- title:
--   BDL26 RXActive Error Transport: inactive q iff
-- statement:
--   The BDL26 RXActive Error Transport construction uses the inactive q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L82-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L82-L92

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.inactive_q_iff (E : Upper S depth i) (q : QCoord S i) :
    q ∉ activeQ S depth i h E ↔
      restrictWordLinear ((rxLq S depth i h).correctionRegion q) E=0 := by sorry
