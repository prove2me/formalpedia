-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_upperStar_subset_inputBlocks
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.upperStar_subset_inputBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:32:39.801197+00:00
-- url     : https://prove2.me/theorems/77a6f792-4621-4bd3-ae4d-5d2590c9d53f
-- title:
--   BDL26 RZPhysical XStar Transport: upper Star subset input Blocks
-- statement:
--   Every actual physical star is covered by its computed finite input blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L248-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L248-L258

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_upperStar_subset_inputBlocks

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.upperStar_subset_inputBlocks (u : FamilyX S depth i.succ) :
    upperStar S depth i u ⊆ inputBlocks S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) := by sorry
