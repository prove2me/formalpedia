-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_map1_with_potential
-- name    : QEC.Coding.BDL26RXQBlockTransport.map1_with_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:15:31.869664+00:00
-- url     : https://prove2.me/theorems/01d61eef-cbc2-440d-aebe-c7b1a1083fb9
-- title:
--   BDL26 RXQBlock Transport: map1 with potential
-- statement:
--   The BDL26 RXQBlock Transport construction uses the map1 with potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L376-L381
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L376-L381

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXQBlockTransport.map1_with_potential (q : QCoord S i) (a b : Upper S depth i)
    (he : hammingSupport (a+b) ⊆ (rxLq S depth i h).correctionRegion q) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h q a b) =
      updated S depth i h a b +
        (indexedFamily S depth).coboundary0 i.succ (potential S depth i h) := by sorry
