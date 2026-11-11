-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_gradient_coordinates
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.lower_gradient_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:29:06.109201+00:00
-- url     : https://prove2.me/theorems/f9ffa7c1-9fdc-4234-8bad-7cadfed31d28
-- title:
--   BDL26 RZPhysical XStar Transport: lower gradient coordinates
-- statement:
--   All three raw gradient cases are evaluated through the original fixed parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L490-L494
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L490-L494

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.lower_gradient_coordinates (x : RZX (Old S depth i) S) (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd x))=
      rzQParity (Old S depth i) S (rzCoboundary0 (Old S depth i) (state S i.val).admissible S
        (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x)) := by sorry
