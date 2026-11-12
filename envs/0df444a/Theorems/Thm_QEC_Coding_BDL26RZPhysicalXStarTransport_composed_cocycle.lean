-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_composed_cocycle
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.composed_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:16:54.433116+00:00
-- url     : https://prove2.me/theorems/497a9251-c9cd-4766-a774-b4ceccb90f26
-- title:
--   BDL26 RZPhysical XStar Transport: composed cocycle
-- statement:
--   The composed full potential is a cocycle boundary under the same upper complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L879-L883
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L879-L883

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.composed_cocycle (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j)) (p : Potential S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary1 (topStep j).succ
      ((indexedFamily S (2*j+4)).coboundary0 (topStep j).succ (composedPotential S j u a b p))=0 := by sorry
