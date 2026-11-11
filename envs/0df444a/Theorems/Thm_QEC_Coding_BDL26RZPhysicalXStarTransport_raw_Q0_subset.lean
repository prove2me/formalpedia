-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_raw_Q0_subset
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.raw_Q0_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:34:22.567198+00:00
-- url     : https://prove2.me/theorems/b7f38d50-9e62-489d-9c4b-59a38c583497
-- title:
--   BDL26 RZPhysical XStar Transport: raw Q0 subset
-- statement:
--   The singleton Q-edge root comes from original admissibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L151-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L151-L161

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.raw_Q0_subset (C : ConstructionState) (S : OddScale) (u : RZX C.presentation S) :
    rawQ0 C.presentation S u ⊆ BDL26RXPhysicalStarTransport.physicalXStar
      C.presentation (rawDown C S u) := by sorry
