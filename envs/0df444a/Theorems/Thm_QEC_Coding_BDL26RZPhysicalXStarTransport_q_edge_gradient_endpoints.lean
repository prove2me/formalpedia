-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_q_edge_gradient_endpoints
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_gradient_endpoints
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:04:34.996922+00:00
-- url     : https://prove2.me/theorems/4ea5d2a6-b40f-4be7-b74e-86a0959bc8de
-- title:
--   BDL26 RZPhysical XStar Transport: q edge gradient endpoints
-- statement:
--   Exact coefficients at both original endpoints, not just an equality after lower parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L509-L519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L509-L519

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_gradient_endpoints (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))
      (.inr ⟨q,qDoubleCylinderEdgeStart (transposePresentation (Old S depth i)) q S e⟩)=1 ∧
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))
      (.inr ⟨q,qDoubleCylinderEdgeEnd (transposePresentation (Old S depth i)) q S e⟩)=1 := by sorry
