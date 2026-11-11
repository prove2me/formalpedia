-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_q_edge_weight
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:38:54.126517+00:00
-- url     : https://prove2.me/theorems/285d36ba-ff79-4302-b61a-61d9a4cc701d
-- title:
--   BDL26 RZPhysical XStar Transport: q edge weight
-- statement:
--   The BDL26 RZPhysical XStar Transport construction uses the q edge weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L351-L355
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L351-L355

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_weight (above : 3 ≤ i.val) (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) (a b : Upper S depth i)
    (he : Localized S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))) a b) :
    HammingWeight (lowerError S depth i odd a b) ≤ 1 := by sorry
