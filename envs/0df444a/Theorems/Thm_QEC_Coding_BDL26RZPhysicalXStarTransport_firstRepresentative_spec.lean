-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_firstRepresentative_spec
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.firstRepresentative_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:45:31.155383+00:00
-- url     : https://prove2.me/theorems/1b2dfa81-25f8-4b71-b172-3e33bfafab9d
-- title:
--   BDL26 RZPhysical XStar Transport: first Representative spec
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the first Representative spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L687-L690
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L687-L690

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.firstRepresentative_spec (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    (indexedFamily S (2*j+4)).coboundary1 (rxStep j).succ (firstRepresentative S j a)=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse.val := by sorry
