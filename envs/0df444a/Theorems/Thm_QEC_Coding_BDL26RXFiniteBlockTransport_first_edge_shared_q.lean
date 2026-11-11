-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_first_edge_shared_q
-- name    : QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_shared_q
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:02:56.61103+00:00
-- url     : https://prove2.me/theorems/3d284ca5-9084-44f6-abcd-bc192e3475e1
-- title:
--   BDL26 RXFinite Block Transport: first edge shared q
-- statement:
--   The real seed overlap: Q label four is incident to both distinct X owners.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L756-L768
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean#L756-L768

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
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26RXFiniteBlockTransport.first_edge_shared_q (S : OddScale) (depth : Nat) (hd : 0<depth) :
    let i : StepIndex depth := ⟨0,hd⟩
    (0 : BaseX)≠1 ∧
      (4 : BaseQubit) ∈ incidentQ S depth i (0 : BaseX) ∧
      (4 : BaseQubit) ∈ incidentQ S depth i (1 : BaseX) := by sorry
