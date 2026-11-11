-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_correction_difference_supported
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.correction_difference_supported
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T16:59:33.053553+00:00
-- url     : https://prove2.me/theorems/46ca2c60-d743-4d09-8fc9-d590f1b89ac1
-- title:
--   BDL26 RZPhysical XStar Transport: correction difference supported
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the correction difference supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L293-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L293-L297

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_correction_difference_supported
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_correction_difference_supported

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.correction_difference_supported (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport ((run S depth i odd a).correction+(run S depth i odd b).correction) ⊆
      zBlocks S depth i odd (Zplus S depth i odd u) := by sorry
