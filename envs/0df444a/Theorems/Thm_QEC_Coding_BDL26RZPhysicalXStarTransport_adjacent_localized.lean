-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_adjacent_localized
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.adjacent_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:44:19.777299+00:00
-- url     : https://prove2.me/theorems/d23b46d4-2c4f-40a2-b56c-fa8b3f59b687
-- title:
--   BDL26 RZPhysical XStar Transport: adjacent localized
-- statement:
--   The RX locality premise is derived, with both actual original coarse inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L784-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L784-L791

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.adjacent_localized (S : OddScale) (j : Nat) (u : FamilyX S (2*j+4) (topStep j).succ)
    (a b : Upper S (2*j+4) (topStep j))
    (he : Localized S (2*j+4) (topStep j) u a b) :
    BDL26RXPhysicalStarTransport.Localized S (2*j+4) (rxStep j) (middleX S j u)
      (firstRepresentative S j a) (secondRepresentative S j a b) := by sorry
