-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_endpoint_transport
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.endpoint_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:39:07.194451+00:00
-- url     : https://prove2.me/theorems/8bf86aee-9e5d-42f9-81a6-4d23be7fc3db
-- title:
--   BDL26 RZPhysical XStar Transport: endpoint transport
-- statement:
--   Either endpoint yields the nonzero old q basis, although the X centre has no raw parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L400-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L400-L419

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.endpoint_transport (above : 3 ≤ i.val) (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S)
    (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    let u := upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))
    let b := a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (edgeEndpointQ S depth i odd q e c)
    ∃ p : Potential S depth i, Pullback S depth i odd {q} (Coordinates.neighborZ (Old S depth i) {q}) a b p ∧
      parent S (i.val+1) (Vertex.x u)=none ∧
      lowerError S depth i odd a b=canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q ∧
      lowerError S depth i odd a b≠0 ∧ HammingWeight (lowerError S depth i odd a b) ≤ 1 := by sorry
