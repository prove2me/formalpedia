-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_potential_delta_zero
-- name    : QEC.Coding.BDL26RXQBlockTransport.potential_delta_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:13:15.562207+00:00
-- url     : https://prove2.me/theorems/747a483a-1ad2-4252-ad8e-2209dee9c513
-- title:
--   BDL26 RXQBlock Transport: potential delta zero
-- statement:
--   The BDL26 RXQBlock Transport construction uses the potential delta zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L331-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L331-L332

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

theorem QEC.Coding.BDL26RXQBlockTransport.potential_delta_zero :
    (indexedFamily S depth).coboundary0 i.succ (potential S depth i h)=0 := by sorry
