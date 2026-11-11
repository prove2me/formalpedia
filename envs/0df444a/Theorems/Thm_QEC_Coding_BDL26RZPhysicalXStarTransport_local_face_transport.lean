-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_local_face_transport
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.local_face_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:37:09.563116+00:00
-- url     : https://prove2.me/theorems/87aaf06b-70ac-4e7d-b3ec-d01e3516bea1
-- title:
--   BDL26 RZPhysical XStar Transport: local face transport
-- statement:
--   The local-face constructor has sharp zero lower error but retains full E as a boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L328-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L328-L349

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.local_face_transport (above : 3 ≤ i.val) (z : (Old S depth i).Z)
    (f : ZDoubleCylinderFace (Old S depth i) z S) (a b : Upper S depth i)
    (he : Localized S depth i (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩))) a b) :
    ∃ p : Potential S depth i, Pullback S depth i odd ∅ {z} a b p ∧
      lowerError S depth i odd a b=0 ∧ HammingWeight (lowerError S depth i odd a b)=0 ∧
      (run S depth i odd a).coarse.val=(run S depth i odd b).coarse.val ∧
      updated S depth i odd a b=(indexedFamily S depth).coboundary0 i.succ p := by sorry
