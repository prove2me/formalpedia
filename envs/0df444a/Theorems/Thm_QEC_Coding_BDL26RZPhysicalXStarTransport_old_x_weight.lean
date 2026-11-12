-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_old_x_weight
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:59:20.685639+00:00
-- url     : https://prove2.me/theorems/27d0c8a3-badc-47f4-be32-ab8b65896738
-- title:
--   BDL26 RZPhysical XStar Transport: old x weight
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the old x weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L357-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L357-L362

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_weight (above : 3 ≤ i.val) (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two)
    (a b : Upper S depth i) (he : Localized S depth i (upperXChart S depth i odd (.inr (x,c))) a b) :
    HammingWeight (lowerError S depth i odd a b) ≤
      (BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) x).card ∧
      (BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) x).card ≤ 7 := by sorry
