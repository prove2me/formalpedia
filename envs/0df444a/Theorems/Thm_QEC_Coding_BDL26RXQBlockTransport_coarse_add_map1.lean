-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_coarse_add_map1
-- name    : QEC.Coding.BDL26RXQBlockTransport.coarse_add_map1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:47:26.927936+00:00
-- url     : https://prove2.me/theorems/0fea0acf-3d21-41a0-9ff1-9a9f3fcc501d
-- title:
--   BDL26 RXQBlock Transport: coarse add map1
-- statement:
--   The BDL26 RXQBlock Transport construction uses the coarse add map1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L567-L573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L567-L573

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

theorem QEC.Coding.BDL26RXQBlockTransport.coarse_add_map1 (a : Upper S depth i) (w : Lower S depth i) :
    (coarseSum S depth i h a (a+((indexedDecoderData S depth).selectedMap i).map1 w)).val =
      (indexedFamily S depth).coboundary1 i.castSucc w := by sorry
