-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_old_x_data
-- name    : QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:54:10.903294+00:00
-- url     : https://prove2.me/theorems/dbd3e159-54aa-4eea-ac6c-1b4624ee5e6b
-- title:
--   BDL26 RZPhysical XStar Transport: old x data
-- statement:
--   The old X and its actual copy tag determine its original nonzero-cell parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L234-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalXStarTransport.lean#L234-L245

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

theorem QEC.Coding.BDL26RZPhysicalXStarTransport.old_x_data (x : (Old S depth i).X) (c : BDL26FiniteTannerSquare.Two) :
    Q0 S depth i odd (upperXChart S depth i odd (.inr (x,c)))=
      BDL26RXPhysicalStarTransport.physicalXStar (Old S depth i) x ∧
    Z0 S depth i odd (upperXChart S depth i odd (.inr (x,c)))=∅ ∧
    downX S depth i odd (upperXChart S depth i odd (.inr (x,c)))=x ∧
    parent S (i.val+1) (Vertex.x (upperXChart S depth i odd (.inr (x,c))))=some (Vertex.x x) := by sorry
