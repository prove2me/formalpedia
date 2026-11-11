-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_retained_closed_transport
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.retained_closed_transport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:09:37.626772+00:00
-- url     : https://prove2.me/theorems/d6f17b43-8d77-4bca-9b9c-85ea3350f4c2
-- title:
--   BDL26 RZPhysical XStar Transport: retained closed transport
-- statement:
--   Full control: equal original syndromes/corrections and zero coarse difference coexist with nonzero lower l.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L550-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L550-L570

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.retained_closed_transport (above : 3 ≤ i.val) (c : BDL26FiniteTannerSquare.Two) (a : Upper S depth i) :
    let u := upperXChart S depth i odd (.inr (retainedX S depth i,c))
    let b := a+gradient S depth i u
    ∃ p : Potential S depth i,
      Pullback S depth i odd (BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) (retainedX S depth i)) ∅ a b p ∧
      parent S (i.val+1) (Vertex.x u)=some (Vertex.x (retainedX S depth i)) ∧
      lowerError S depth i odd a b≠0 ∧
      (run S depth i odd b).correction=(run S depth i odd a).correction ∧
      (run S depth i odd a).coarse.val+(run S depth i odd b).coarse.val=0 ∧
      (indexedFamily S depth).coboundary1 i.castSucc (lowerError S depth i odd a b)=0 ∧
      updated S depth i odd a b=gradient S depth i u := by sorry
