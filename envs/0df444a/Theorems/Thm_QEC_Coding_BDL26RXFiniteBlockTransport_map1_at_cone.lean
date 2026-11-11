-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_at_cone
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.map1_at_cone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:19:08.804691+00:00
-- url     : https://prove2.me/theorems/69eb3c91-10f7-4fe3-aa7b-32f4d37304ce
-- title:
--   BDL26 RXFinite Block Transport: map1 at cone
-- statement:
--   The BDL26 RXFinite Block Transport construction uses the map1 at cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L720-L731
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L720-L731

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

theorem QEC.Coding.BDL26RXFiniteBlockTransport.map1_at_cone (w : Lower S depth i) (q : QCoord S i) :
    ((indexedDecoderData S depth).selectedMap i).map1 w
      (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val = w q := by sorry
