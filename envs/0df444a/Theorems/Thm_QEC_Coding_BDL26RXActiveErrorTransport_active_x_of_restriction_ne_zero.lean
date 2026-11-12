-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXActiveErrorTransport_active_x_of_restriction_ne_zero
-- name    : QEC.Coding.BDL26RXActiveErrorTransport.active_x_of_restriction_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:26:42.229578+00:00
-- url     : https://prove2.me/theorems/d225eefc-45b4-4e18-8458-85859fa3abbc
-- title:
--   BDL26 RXActive Error Transport: active x of restriction ne zero
-- statement:
--   The BDL26 RXActive Error Transport construction uses the active x of restriction ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L94-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean#L94-L98

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

theorem QEC.Coding.BDL26RXActiveErrorTransport.active_x_of_restriction_ne_zero (E : Upper S depth i) (x : XCoord S i)
    (hn : restrictWordLinear ((rxLx S depth i h).correctionRegion x) E≠0) :
    x ∈ activeX S depth i h E := by sorry
