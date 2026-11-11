-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_incidentWitness_mem
-- name    : QEC.Coding.BDL26RXQBlockTransport.incidentWitness_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:32:57.781958+00:00
-- url     : https://prove2.me/theorems/2b8831de-384d-42d6-9f0f-65f598ae2e9b
-- title:
--   BDL26 RXQBlock Transport: incident Witness mem
-- statement:
--   The BDL26 RXQBlock Transport construction uses the incident Witness mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L638-L641
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXQBlockTransport.lean#L638-L641

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

theorem QEC.Coding.BDL26RXQBlockTransport.incidentWitness_mem (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (q : QCoord S i) :
    (state S i.val).presentation.qz q (incidentWitness S i q)=true := by sorry
