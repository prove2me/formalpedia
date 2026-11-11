-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_supported
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.lower_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:49:11.165193+00:00
-- url     : https://prove2.me/theorems/70095524-95a2-4bc7-9f76-a29d8c00e88e
-- title:
--   BDL26 RZPhysical XStar Transport: lower supported
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the lower supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L276-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L276-L280

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_lower_supported
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_supported

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.lower_supported (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) : hammingSupport (lowerError S depth i odd a b) ⊆ Q0 S depth i odd u := by sorry
