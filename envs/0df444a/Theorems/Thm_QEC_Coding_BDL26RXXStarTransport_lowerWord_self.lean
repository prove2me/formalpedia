-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lowerWord_self
-- name    : QEC.Coding.BDL26RXXStarTransport.lowerWord_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:57:45.763201+00:00
-- url     : https://prove2.me/theorems/f3fedbc4-c75c-4597-a322-afcea8f1e9bf
-- title:
--   BDL26 RXXStar Transport: lower Word self
-- statement:
--   The BDL26 RXXStar Transport construction uses the lower Word self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L433-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L433-L437

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lowerWord_self
attribute [local simp] QEC.Coding.BDL26RXQBlockTransport.lowerWord_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.lowerWord_self (x : XCoord S i) (a : Upper S depth i) :
    lowerWord S depth i h x a a=0 := by sorry
