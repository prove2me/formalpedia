-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_lower_physical_supported
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.lower_physical_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:27:36.979438+00:00
-- url     : https://prove2.me/theorems/742b607a-be0f-4a3d-b70f-8ee654215b78
-- title:
--   BDL26 RZPhysical XStar Transport: lower physical supported
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the lower physical supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L282-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L282-L285

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.lower_physical_supported (above : 3 ≤ i.val) (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) : hammingSupport (lowerError S depth i odd a b) ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (downX S depth i odd u) := by sorry
