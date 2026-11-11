-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_edgeEndpoint_incident
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.edgeEndpoint_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:39:20.341948+00:00
-- url     : https://prove2.me/theorems/20df858f-b9c1-4503-b5a2-edd3ece251ad
-- title:
--   BDL26 RZPhysical XStar Transport: edge Endpoint incident
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the edge Endpoint incident property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L384-L397
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L384-L397

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.edgeEndpoint_incident (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S)
    (c : BDL26FiniteTannerSquare.Two) :
    (state S (i.val+1)).presentation.xq
      (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))) (edgeEndpointQ S depth i odd q e c)=true := by sorry
