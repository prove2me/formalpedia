-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_delta_delta_zero
-- name    : QEC.Coding.BDL26RXQBlockTransport.potential_delta_delta_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:13:47.796882+00:00
-- url     : https://prove2.me/theorems/f015302d-4d74-403c-9275-93653c2a28d9
-- title:
--   BDL26 RXQBlock Transport: potential delta delta zero
-- statement:
--   The BDL26 RXQBlock Transport construction uses the potential delta delta zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L334-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L334-L337

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

theorem QEC.Coding.BDL26RXQBlockTransport.potential_delta_delta_zero :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h))=0 := by sorry
