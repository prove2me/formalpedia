-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_lower_add_map1
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.lower_add_map1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:20:33.650195+00:00
-- url     : https://prove2.me/theorems/26290027-9f94-452d-adb3-00ac0d3e5bb8
-- title:
--   BDL26 RXFinite Block Transport: lower add map1
-- statement:
--   Actual map1-shift invariance fixes the literal lower word for every w.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L734-L738
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L734-L738

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXFiniteBlockTransport.lower_add_map1 (a : Upper S depth i) (w : Lower S depth i) :
    L S depth i h ∅ a (a+((indexedDecoderData S depth).selectedMap i).map1 w)=w := by sorry
