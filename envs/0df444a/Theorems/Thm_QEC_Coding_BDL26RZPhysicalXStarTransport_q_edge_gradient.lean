-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_q_edge_gradient
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_gradient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:03:45.200423+00:00
-- url     : https://prove2.me/theorems/f8b9b6e0-30e4-4e23-80b5-11231b5a850c
-- title:
--   BDL26 RZPhysical XStar Transport: q edge gradient
-- statement:
--   Both endpoints cancel under lower parity, while the complete upper expansion remains.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L497-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L497-L506

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_gradient (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) (a : Upper S depth i) :
    read1 S depth i odd (gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=
      rzMap1QEdgeDelta0BasisImage (Old S depth i) (state S i.val).admissible S q e ∧
    lowerError S depth i odd a (a+gradient S depth i (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=0 := by sorry
