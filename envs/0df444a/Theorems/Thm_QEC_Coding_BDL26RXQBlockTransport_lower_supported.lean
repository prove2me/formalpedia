-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_lower_supported
-- name    : QEC.Coding.BDL26RXQBlockTransport.lower_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:14:37.959358+00:00
-- url     : https://prove2.me/theorems/95a788cf-16f6-406b-a86b-b6833a8db084
-- title:
--   BDL26 RXQBlock Transport: lower supported
-- statement:
--   The BDL26 RXQBlock Transport construction uses the lower supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L406-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L406-L411

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

theorem QEC.Coding.BDL26RXQBlockTransport.lower_supported (q : QCoord S i) (a b : Upper S depth i) :
    hammingSupport (lowerWord S depth i h q a b) ⊆ {q} := by sorry
