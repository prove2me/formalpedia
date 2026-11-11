-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_parent_chart
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.parent_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:23:09.939315+00:00
-- url     : https://prove2.me/theorems/57178cdf-cb03-4709-86ea-7ecfc98a7dbc
-- title:
--   BDL26 RZPhysical XStar Transport: parent chart
-- statement:
--   Exact whole-Vertex cast computes none/none/some, rather than an X owner guess.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L198-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L198-L203

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_parent_chart

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.parent_chart (x : RZX (Old S depth i) S) :
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd x))=
      rawParent (Old S depth i) S x := by sorry
