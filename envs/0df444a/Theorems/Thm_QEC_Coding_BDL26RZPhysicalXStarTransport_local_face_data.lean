-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_local_face_data
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.local_face_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:32:07.989316+00:00
-- url     : https://prove2.me/theorems/6c350cee-226e-4636-8c19-86750dea3348
-- title:
--   BDL26 RZPhysical XStar Transport: local face data
-- statement:
--   Exact constructor table: the local face computes no Q block and no raw parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L206-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L206-L216

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.local_face_data (z : (Old S depth i).Z) (f : ZDoubleCylinderFace (Old S depth i) z S) :
    Q0 S depth i odd (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩)))=∅ ∧
    Z0 S depth i odd (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩)))={z} ∧
    downX S depth i odd (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩)))=(state S i.val).selectedX ∧
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd (.inl (.inl ⟨z,f⟩))))=none := by sorry
