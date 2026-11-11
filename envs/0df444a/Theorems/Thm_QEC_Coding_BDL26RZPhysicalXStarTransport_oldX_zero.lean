-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_oldX_zero
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.oldX_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:36:17.808951+00:00
-- url     : https://prove2.me/theorems/dcf74517-fdec-4d5f-9be6-c95619da9c12
-- title:
--   BDL26 RZPhysical XStar Transport: old X zero
-- statement:
--   Same-p both-copy zero, independently usable with the literal full Pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L322-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L322-L325

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_oldX_zero

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.oldX_zero (u : FamilyX S depth i.succ) (a b : Upper S depth i) (p : Potential S depth i)
    (hp : Pullback S depth i odd (Q0 S depth i odd u) (Z0 S depth i odd u) a b p)
    (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) : read0 S depth i odd p (.inr (x,c))=0 := by sorry
