-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_old_x_gradient
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_gradient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:42:17.929057+00:00
-- url     : https://prove2.me/theorems/3817ebe3-0762-4121-913c-c5dacff7d3a6
-- title:
--   BDL26 RZPhysical XStar Transport: old x gradient
-- statement:
--   A closed old-X gradient survives as its nontruncated lower old-X gradient, for either copy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L529-L533
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L529-L533

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_gradient (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inr (x,c))))=
      tannerCoboundary0 (Old S depth i) (canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) x) := by sorry
