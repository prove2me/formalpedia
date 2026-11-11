-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_depth_four_indices
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.depth_four_indices
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:16:00.704328+00:00
-- url     : https://prove2.me/theorems/64a20ebf-71dd-4f6f-a4d0-2beff8bee34b
-- title:
--   BDL26 RZPhysical XStar Transport: depth four indices
-- statement:
--   Literal arithmetic C4→C3→C2; no decoder below the stopped boundary is introduced.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L941-L942
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L941-L942

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.depth_four_indices : (topStep 0).val=3 ∧ (rxStep 0).val=2 ∧
    (topStep 0).succ.val=4 ∧ (rxStep 0).castSucc.val=2 := by sorry
