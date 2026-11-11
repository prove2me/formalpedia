-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_q_edge_data
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:34:38.242206+00:00
-- url     : https://prove2.me/theorems/019919d1-542c-40e6-bc17-5185d284887e
-- title:
--   BDL26 RZPhysical XStar Transport: q edge data
-- statement:
--   Exact Q-edge table, including all old Z neighbours and an incident computed centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L219-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L219-L231

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.q_edge_data (q : (Old S depth i).Q)
    (e : QDoubleCylinderEdge (transposePresentation (Old S depth i)) q S) :
    Q0 S depth i odd (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩)))={q} ∧
    Z0 S depth i odd (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩)))=Coordinates.neighborZ (Old S depth i) {q} ∧
    downX S depth i odd (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩)))=
      ((state S i.val).admissible.toTannerSquareAdmissible.xqRoot q).1 ∧
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd (.inl (.inr ⟨q,e⟩))))=none := by sorry
