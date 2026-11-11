-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_gradient_coordinates
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.gradient_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:41:54.565834+00:00
-- url     : https://prove2.me/theorems/f003b92b-1a66-414d-b347-8f3600589088
-- title:
--   BDL26 RZPhysical XStar Transport: gradient coordinates
-- statement:
--   The full global gradient is exactly the literal raw gradient under the actual charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L483-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L483-L487

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.gradient_coordinates (x : RZX (Old S depth i) S) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd x))=
      rzCoboundary0 (Old S depth i) (state S i.val).admissible S
        (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x) := by sorry
