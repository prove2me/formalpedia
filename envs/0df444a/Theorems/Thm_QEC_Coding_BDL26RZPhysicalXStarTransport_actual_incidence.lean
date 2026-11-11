-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_actual_incidence
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.actual_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:33:53.961061+00:00
-- url     : https://prove2.me/theorems/16f9b1d5-e169-4169-925e-848f1c737620
-- title:
--   BDL26 RZPhysical XStar Transport: actual incidence
-- statement:
--   Literal xq transport along the actual RZ successor equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L185-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L185-L189

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_actual_incidence

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.actual_incidence (u : FamilyX S depth i.succ) (r : FamilyQ S depth i.succ) :
    (state S (i.val+1)).presentation.xq u r=
      rzXQIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
        (coord0 S depth i odd u) (coord1 S depth i odd r) := by sorry
